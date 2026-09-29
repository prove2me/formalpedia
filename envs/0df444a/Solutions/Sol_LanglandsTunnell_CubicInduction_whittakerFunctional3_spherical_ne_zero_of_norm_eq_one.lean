-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6a8b7c78-ec9e-52f0-9d25-55e829c30205

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one

set_option autoImplicit false

noncomputable section

section PartA

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

namespace CSNV

section Basic

variable (v : HeightOneSpectrum (𝓞 ℚ))

def unipotentBall (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧
    Valued.v p.2.2 ≤ WithZero.exp (2 * c)}

theorem upperUnipotent3_mul_upperUnipotent3 (x y z x' y' z' : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 x' y' z'
      = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Basic

section UnipotentBall

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem zero_mem_unipotentBall (c : ℤ) :
    ((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ)) ∈ unipotentBall v c := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem exp_two_mul (c : ℤ) :
    (WithZero.exp (2 * c) : WithZero (Multiplicative ℤ)) = WithZero.exp c * WithZero.exp c := by
  rw [two_mul, WithZero.exp_add]

variable {v}

theorem mem_unipotentBall_mul {c : ℤ} {x y z x' y' z' : v.adicCompletion ℚ} (h : (x, y, z) ∈ unipotentBall v c)
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

theorem mem_unipotentBall_inv {c : ℤ} {x y z : v.adicCompletion ℚ} (h : (x, y, z) ∈ unipotentBall v c) :
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

theorem upperUnipotent3_mul_upperUnipotent3_neg (x y z : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 (-x) (-y) (x * y - z) = upperUnipotent3 0 0 0 := by
  rw [upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

end UnipotentBall

section WhittakerDetector

open MeasureTheory

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem isClopen_valued_le (c : ℤ) :
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

theorem isCompact_valued_le (c : ℤ) :
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

theorem unipotentBall_eq_prod (c : ℤ) :
    unipotentBall v c =
      {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} ×ˢ
        ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)}) := by
  ext p
  simp only [unipotentBall, Set.mem_setOf_eq, Set.mem_prod]

theorem isClopen_unipotentBall (c : ℤ) : IsClopen (unipotentBall v c) := by
  rw [unipotentBall_eq_prod]
  exact (isClopen_valued_le v c).prod ((isClopen_valued_le v c).prod (isClopen_valued_le v (2 * c)))

theorem isCompact_unipotentBall (c : ℤ) : IsCompact (unipotentBall v c) := by
  rw [unipotentBall_eq_prod]
  exact (isCompact_valued_le v c).prod ((isCompact_valued_le v c).prod (isCompact_valued_le v (2 * c)))

theorem unipotentBall_mono {c d : ℤ} (hcd : c ≤ d) : unipotentBall v c ⊆ unipotentBall v d := by
  intro p hp
  simp only [unipotentBall, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h₁, h₂, h₃⟩ := hp
  exact ⟨h₁.trans (WithZero.exp_le_exp.mpr hcd), h₂.trans (WithZero.exp_le_exp.mpr hcd),
    h₃.trans (WithZero.exp_le_exp.mpr (by omega))⟩

theorem exists_valued_le_exp (x : v.adicCompletion ℚ) : ∃ n : ℤ, Valued.v x ≤ WithZero.exp n := by
  by_cases hx : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), (WithZero.exp_log hx).symm.le⟩

theorem exists_mem_unipotentBall (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ∃ c : ℤ, p ∈ unipotentBall v c := by
  obtain ⟨a, ha⟩ := exists_valued_le_exp v p.1
  obtain ⟨b, hb⟩ := exists_valued_le_exp v p.2.1
  obtain ⟨d, hd⟩ := exists_valued_le_exp v p.2.2
  refine ⟨max (max a b) (max d 0), ?_⟩
  simp only [unipotentBall, Set.mem_setOf_eq]
  exact ⟨ha.trans (WithZero.exp_le_exp.mpr (by omega)), hb.trans (WithZero.exp_le_exp.mpr (by omega)),
    hd.trans (WithZero.exp_le_exp.mpr (by omega))⟩

theorem valued_add_le_of_le {x y : v.adicCompletion ℚ} {γ : WithZero (Multiplicative ℤ)}
    (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) : Valued.v (x + y) ≤ γ :=
  (Valued.v.map_add x y).trans (max_le hx hy)

def coordTranslate (q p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

theorem upperUnipotent3_mul_eq_coordTranslate
    (p q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) * upperUnipotent3 q.1 q.2.1 q.2.2 =
      upperUnipotent3 (coordTranslate v q p).1 (coordTranslate v q p).2.1 (coordTranslate v q p).2.2 :=
  upperUnipotent3_mul_upperUnipotent3 v p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2

theorem coordTranslate_mem_unipotentBall_iff {c : ℤ}
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

def coordTranslateHomeomorph (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
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

theorem continuous_upperUnipotent3_coords :
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

abbrev borelAdicCompletion : MeasurableSpace (v.adicCompletion ℚ) := borel (v.adicCompletion ℚ)

attribute [local instance] borelAdicCompletion

theorem borelSpace_adicCompletion : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩

attribute [local instance] borelSpace_adicCompletion

noncomputable abbrev coordHaar :
    Measure (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  (Measure.addHaar : Measure (v.adicCompletion ℚ)).prod
    ((Measure.addHaar : Measure (v.adicCompletion ℚ)).prod (Measure.addHaar : Measure (v.adicCompletion ℚ)))

theorem measurePreserving_coordTranslate
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

theorem integral_comp_coordTranslate
    (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)
    (G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    ∫ p, G (coordTranslate v q p) ∂(coordHaar v) = ∫ p, G p ∂(coordHaar v) :=
  (measurePreserving_coordTranslate v q).integral_comp
    (coordTranslateHomeomorph v q).measurableEmbedding G

noncomputable def detectorIntegrand (ψ : AddChar (v.adicCompletion ℚ) ℂ) (c : ℤ) (u : LocalGL3 v → ℂ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  (unipotentBall v c).indicator
    (fun p => ψ (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) p

noncomputable def whittakerDetector (ψ : AddChar (v.adicCompletion ℚ) ℂ) (c : ℤ) (u : LocalGL3 v → ℂ) : ℂ :=
  ∫ p, detectorIntegrand v ψ c u p ∂(coordHaar v)

theorem integrable_detectorIntegrand {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : Continuous ψ) (c : ℤ)
    {u : LocalGL3 v → ℂ} (hu : Continuous u) : Integrable (detectorIntegrand v ψ c u) (coordHaar v) := by
  have hcont : Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      ψ (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) :=
    (hψ.comp (by fun_prop)).mul (hu.comp (continuous_const.mul (continuous_upperUnipotent3_coords v)))
  exact (integrable_indicator_iff (isClopen_unipotentBall v c).isOpen.measurableSet).mpr
    (hcont.continuousOn.integrableOn_compact (isCompact_unipotentBall v c))

noncomputable def detectorForm (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
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

theorem detectorForm_apply (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψ : Continuous ψ) (c : ℤ) (F : ↥(principalSeries3 v χ)) :
    detectorForm v χ hψ c F = whittakerDetector v ψ c F.1 := rfl

theorem detector_rightTranslate (ψ : AddChar (v.adicCompletion ℚ) ℂ) {c : ℤ}
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

theorem detector_eq_of_apply_eq_ite (ψ : AddChar (v.adicCompletion ℚ) ℂ) {m : ℤ}
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

theorem coordHaar_real_unipotentBall_pos (c : ℤ) : 0 < (coordHaar v).real (unipotentBall v c) := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ (isCompact_unipotentBall v c).measure_lt_top.ne
  exact ((isClopen_unipotentBall v c).isOpen.measure_pos (coordHaar v) ⟨_, zero_mem_unipotentBall v c⟩).ne'

theorem continuous_addChar_of_eq_one_on_ball (ψ : AddChar (v.adicCompletion ℚ) ℂ) (m : ℤ)
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

theorem whittaker_apply_ne_zero_of_detector_ne_zero (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (v.adicCompletion ℚ) ℂ) {m : ℤ}
    (hm : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψ x = 1) (hψne : ψ ≠ 1)
    (f : ↥(principalSeries3 v χ)) (c₀ : ℤ)
    (hdet : ∀ c : ℤ, c₀ ≤ c → whittakerDetector v ψ c (f : LocalGL3 v → ℂ) ≠ 0)
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerFunctional3 ψ Λ) (hΛne : Λ ≠ 0) :
    Λ f ≠ 0 := by
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
    rw [detectorForm_apply] at h0
    exact hdet (max c c₀) (le_max_right c c₀) h0
  obtain ⟨L, hLf, hLmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hf_notMem inferInstance
  have hLW : IsWhittakerFunctional3 ψ L := by
    intro x y z F
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
  have hL0 : L ≠ 0 := fun h => hLf (by rw [h]; rfl)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isWhittakerFunctional3 v χ ψ hψne L Λ hLW hL0 hΛ
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΛne (by rw [hc, zero_smul])
  rw [hc, LinearMap.smul_apply, smul_eq_mul]
  exact mul_ne_zero hc0 hLf

end WhittakerDetector

end CSNV

end PartA

section PartB

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

namespace CSNV

section Iwasawa

variable (v : HeightOneSpectrum (𝓞 ℚ))

def mi01 (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) : v.adicCompletion ℚ := M 1 0 * M 2 1 - M 1 1 * M 2 0
def mi02 (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) : v.adicCompletion ℚ := M 1 0 * M 2 2 - M 1 2 * M 2 0
def mi12 (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) : v.adicCompletion ℚ := M 1 1 * M 2 2 - M 1 2 * M 2 1

theorem det_eq_expansion (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    M.det = M 0 0 * mi12 v M - M 0 1 * mi02 v M + M 0 2 * mi01 v M := by
  rw [Matrix.det_fin_three]
  simp only [mi01, mi02, mi12]
  ring

variable {v}

theorem valued_det_le_one {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  have hp : ∀ a b c d e f : Fin 3, Valued.v (M a b * M c d * M e f) ≤ 1 := fun a b c d e f => by
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (h _ _) (h _ _)) (h _ _)
  rw [Matrix.det_fin_three]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hp _ _ _ _ _ _))
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (hp _ _ _ _ _ _))
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (hp _ _ _ _ _ _))
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hp _ _ _ _ _ _))
  exact (Valuation.map_sub _ _ _).trans (max_le (hp _ _ _ _ _ _) (hp _ _ _ _ _ _))

theorem valued_mi01_le_one {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v (mi01 v M) ≤ 1 := by
  unfold mi01
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (h _ _) (h _ _)

theorem valued_mi02_le_one {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v (mi02 v M) ≤ 1 := by
  unfold mi02
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (h _ _) (h _ _)

theorem valued_mi12_le_one {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v (mi12 v M) ≤ 1 := by
  unfold mi12
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (h _ _) (h _ _)

theorem eq_one_of_mul_eq_one_of_le {a b : WithZero (Multiplicative ℤ)} (hab : a * b = 1) (ha : a ≤ 1) (hb : b ≤ 1) :
    a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  push Not at hlt
  exact absurd hab (ne_of_lt (mul_lt_one_of_lt_of_le hlt hb))

variable (v)

theorem valued_det_eq_one {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det = 1 := by
  obtain ⟨h1, h2⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk
  have hprod : Valued.v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det *
      Valued.v ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  exact eq_one_of_mul_eq_one_of_le hprod (valued_det_le_one h1) (valued_det_le_one h2)

theorem exists_valued_bottom_eq_one {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ∃ j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j) = 1 := by
  obtain ⟨h1, h2⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk
  by_contra hne
  push Not at hne
  have hlt : ∀ j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j) < 1 := fun j =>
    lt_of_le_of_ne (h1 2 j) (hne j)
  have hone : ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
      ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) 2 2 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  have hterm : ∀ l, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 l *
      ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l 2) < 1 := fun l => by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le (hlt l) (h2 l 2)
  have hlt' : Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
      ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) 2 2) < 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ (hterm 2))
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hterm 0) (hterm 1))
  rw [hone, map_one] at hlt'
  exact lt_irrefl _ hlt'

theorem valued_minor_eq_one {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v (mi01 v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) = 1 ∨
      Valued.v (mi02 v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) = 1 ∨
      Valued.v (mi12 v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) = 1 := by
  obtain ⟨h1, h2⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk
  set M := (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hM
  have hdet := valued_det_eq_one v hk
  rw [det_eq_expansion] at hdet
  have hA : Valued.v (M 0 0 * mi12 v M) ≤ Valued.v (mi12 v M) := by
    rw [map_mul]; exact mul_le_of_le_one_left' (h1 0 0)
  have hB : Valued.v (M 0 1 * mi02 v M) ≤ Valued.v (mi02 v M) := by
    rw [map_mul]; exact mul_le_of_le_one_left' (h1 0 1)
  have hC : Valued.v (M 0 2 * mi01 v M) ≤ Valued.v (mi01 v M) := by
    rw [map_mul]; exact mul_le_of_le_one_left' (h1 0 2)
  have hle : (1 : WithZero (Multiplicative ℤ)) ≤
      max (max (Valued.v (mi12 v M)) (Valued.v (mi02 v M))) (Valued.v (mi01 v M)) := by
    rw [← hdet]
    refine (Valuation.map_add _ _ _).trans (max_le_max ?_ hC)
    exact (Valuation.map_sub _ _ _).trans (max_le_max hA hB)
  rcases le_max_iff.mp hle with h | h
  · rcases le_max_iff.mp h with h' | h'
    · exact Or.inr (Or.inr (le_antisymm (valued_mi12_le_one h1) h'))
    · exact Or.inr (Or.inl (le_antisymm (valued_mi02_le_one h1) h'))
  · exact Or.inl (le_antisymm (valued_mi01_le_one h1) h)

theorem antidiagonal3_mul_upperUnipotent3_coe (x y z : v.adicCompletion ℚ) :
    ((antidiagonal3 v * upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 0, 1; 0, 1, y; 1, x, z] := by
  rw [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable {v}

theorem bottom_row_eq {x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (j : Fin 3) :
    ((upperUnipotent3 x' y' z' * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j =
      d 2 * (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j := by
  have hnt : ∀ l, ((upperUnipotent3 x' y' z' * t : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 l =
      if l = 2 then d 2 else 0 := by
    intro l
    rw [Units.val_mul, htd, Matrix.mul_diagonal, upperUnipotent3_coe]
    fin_cases l <;> simp
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hnt, hnt, hnt]
  simp

theorem middle_row_eq {x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (j : Fin 3) :
    ((upperUnipotent3 x' y' z' * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 j =
      d 1 * (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 j +
        y' * d 2 * (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j := by
  have hnt : ∀ l, ((upperUnipotent3 x' y' z' * t : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 l =
      if l = 1 then d 1 else if l = 2 then y' * d 2 else 0 := by
    intro l
    rw [Units.val_mul, htd, Matrix.mul_diagonal, upperUnipotent3_coe]
    fin_cases l <;> simp
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hnt, hnt, hnt]
  simp

theorem mi01_eq {x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    mi01 v ((upperUnipotent3 x' y' z' * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      d 1 * d 2 * mi01 v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
  simp only [mi01, bottom_row_eq htd, middle_row_eq htd]
  ring

theorem mi02_eq {x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    mi02 v ((upperUnipotent3 x' y' z' * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      d 1 * d 2 * mi02 v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
  simp only [mi02, bottom_row_eq htd, middle_row_eq htd]
  ring

theorem mi12_eq {x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    mi12 v ((upperUnipotent3 x' y' z' * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      d 1 * d 2 * mi12 v (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
  simp only [mi12, bottom_row_eq htd, middle_row_eq htd]
  ring

theorem det_eq_of_iwasawa {x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    ((upperUnipotent3 x' y' z' * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det =
      d 0 * d 1 * d 2 * (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det := by
  have h1 : Matrix.det !![(1 : v.adicCompletion ℚ), x', z'; 0, 1, y'; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, upperUnipotent3_coe, h1, htd,
    Matrix.det_diagonal, Fin.prod_univ_three, one_mul]

theorem iwasawa_invariants {x y z x' y' z' : v.adicCompletion ℚ} {t k : LocalGL3 v}
    {d : Fin 3 → v.adicCompletion ℚ} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (htd : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (h : antidiagonal3 v * upperUnipotent3 x y z = upperUnipotent3 x' y' z' * t * k) :
    Valued.v (d 2) = max 1 (max (Valued.v x) (Valued.v z)) ∧
      Valued.v (d 1) * Valued.v (d 2) = max 1 (max (Valued.v y) (Valued.v (z - x * y))) ∧
      Valued.v (d 0) * Valued.v (d 1) * Valued.v (d 2) = 1 := by
  obtain ⟨hk1, hk2⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk
  set K3 := (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hK3
  have hg := antidiagonal3_mul_upperUnipotent3_coe v x y z
  rw [h] at hg
  have hrow : ∀ j, d 2 * K3 2 j = !![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, y; 1, x, z] 2 j := fun j => by
    rw [← bottom_row_eq htd j, hg]
  have hr0 : d 2 * K3 2 0 = 1 := by simpa using hrow 0
  have hr1 : d 2 * K3 2 1 = x := by simpa using hrow 1
  have hr2 : d 2 * K3 2 2 = z := by simpa using hrow 2
  have hm01 : d 1 * d 2 * mi01 v K3 = -1 := by
    rw [← mi01_eq htd, hg]; simp [mi01]
  have hm02 : d 1 * d 2 * mi02 v K3 = -y := by
    rw [← mi02_eq htd, hg]; simp [mi02]
  have hm12 : d 1 * d 2 * mi12 v K3 = z - x * y := by
    rw [← mi12_eq htd, hg]; simp [mi12]; ring
  have hdet : d 0 * d 1 * d 2 * K3.det = -1 := by
    rw [← det_eq_of_iwasawa htd, hg]; simp [Matrix.det_fin_three]
  have hE2 : ∀ j, Valued.v (!![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, y; 1, x, z] 2 j) ≤
      max 1 (max (Valued.v x) (Valued.v z)) := by
    intro j
    fin_cases j <;> simp
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm ?_ (max_le ?_ (max_le ?_ ?_))
    · obtain ⟨j, hj⟩ := exists_valued_bottom_eq_one v hk
      have : Valued.v (d 2) = Valued.v (d 2 * K3 2 j) := by rw [map_mul, hj, mul_one]
      rw [this, hrow j]
      exact hE2 j
    · have h0 : Valued.v (d 2 * K3 2 0) ≤ Valued.v (d 2) := by
        rw [map_mul]; exact mul_le_of_le_one_right' (hk1 2 0)
      rwa [hr0, map_one] at h0
    · rw [← hr1, map_mul]; exact mul_le_of_le_one_right' (hk1 2 1)
    · rw [← hr2, map_mul]; exact mul_le_of_le_one_right' (hk1 2 2)
  · rw [← map_mul]
    refine le_antisymm ?_ (max_le ?_ (max_le ?_ ?_))
    · rcases valued_minor_eq_one v hk with hj | hj | hj
      · rw [show Valued.v (d 1 * d 2) = Valued.v (d 1 * d 2 * mi01 v K3) by rw [map_mul _ _ (mi01 v K3), hj, mul_one],
          hm01, Valuation.map_neg, map_one]
        exact le_max_left _ _
      · rw [show Valued.v (d 1 * d 2) = Valued.v (d 1 * d 2 * mi02 v K3) by rw [map_mul _ _ (mi02 v K3), hj, mul_one],
          hm02, Valuation.map_neg]
        exact le_max_of_le_right (le_max_left _ _)
      · rw [show Valued.v (d 1 * d 2) = Valued.v (d 1 * d 2 * mi12 v K3) by rw [map_mul _ _ (mi12 v K3), hj, mul_one],
          hm12]
        exact le_max_of_le_right (le_max_right _ _)
    · have h0 : Valued.v (d 1 * d 2 * mi01 v K3) ≤ Valued.v (d 1 * d 2) := by
        rw [map_mul _ _ (mi01 v K3)]; exact mul_le_of_le_one_right' (valued_mi01_le_one hk1)
      rwa [hm01, Valuation.map_neg, map_one] at h0
    · rw [← Valuation.map_neg, ← hm02, map_mul _ _ (mi02 v K3)]
      exact mul_le_of_le_one_right' (valued_mi02_le_one hk1)
    · rw [← hm12, map_mul _ _ (mi12 v K3)]
      exact mul_le_of_le_one_right' (valued_mi12_le_one hk1)
  · have hk3 : Valued.v K3.det = 1 := valued_det_eq_one v hk
    have := congrArg Valued.v hdet
    rw [map_mul, hk3, mul_one, Valuation.map_neg, map_one, map_mul, map_mul] at this
    exact this

end Iwasawa

section Value

variable (v : HeightOneSpectrum (𝓞 ℚ))

def qv : ℂ := (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ)

theorem qv_ne_zero : qv v ≠ 0 := natCast_natCard_quot_ne_zero v

theorem one_lt_qv_re : (1 : ℝ) < (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) := by
  exact_mod_cast one_lt_natCard_quot v

def alpha (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (i : Fin 3) : ℂ :=
  ((χ i (uniformizerUnit ℚ v) : ℂˣ) : ℂ)

theorem alpha_ne_zero (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (i : Fin 3) : alpha v χ i ≠ 0 :=
  Units.ne_zero _

def PP (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : ℂ := alpha v χ 0 * (alpha v χ 1)⁻¹ * (qv v)⁻¹
def QQ (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : ℂ := alpha v χ 1 * (alpha v χ 2)⁻¹ * (qv v)⁻¹

def e2 (x z : v.adicCompletion ℚ) : WithZero (Multiplicative ℤ) := max 1 (max (Valued.v x) (Valued.v z))
def e1 (x y z : v.adicCompletion ℚ) : WithZero (Multiplicative ℤ) :=
  max 1 (max (Valued.v y) (Valued.v (z - x * y)))

theorem one_le_e2 (x z : v.adicCompletion ℚ) : 1 ≤ e2 v x z := le_max_left _ _
theorem one_le_e1 (x y z : v.adicCompletion ℚ) : 1 ≤ e1 v x y z := le_max_left _ _
theorem e2_ne_zero (x z : v.adicCompletion ℚ) : e2 v x z ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_e2 v x z))
theorem e1_ne_zero (x y z : v.adicCompletion ℚ) : e1 v x y z ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_e1 v x y z))
theorem log_e2_nonneg (x z : v.adicCompletion ℚ) : 0 ≤ (e2 v x z).log := by
  rw [← WithZero.log_one]; exact (WithZero.log_le_log one_ne_zero (e2_ne_zero v x z)).mpr (one_le_e2 v x z)
theorem log_e1_nonneg (x y z : v.adicCompletion ℚ) : 0 ≤ (e1 v x y z).log := by
  rw [← WithZero.log_one]; exact (WithZero.log_le_log one_ne_zero (e1_ne_zero v x y z)).mpr (one_le_e1 v x y z)

variable {v}

theorem char_eq_alpha_zpow (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ x : (v.adicCompletion ℚ)ˣ, ‖(x : v.adicCompletion ℚ)‖ = 1 → χ x = 1)
    (a : (v.adicCompletion ℚ)ˣ) (n : ℤ) (ha : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp n) :
    ((χ a : ℂˣ) : ℂ) = ((χ (uniformizerUnit ℚ v) : ℂˣ) : ℂ) ^ (-n) := by
  set ϖ := uniformizerUnit ℚ v with hϖ
  have hval : Valued.v ((a * ϖ ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, ha, hϖ, valued_uniformizerUnit,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hnorm : ‖((a * ϖ ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = 1 :=
    le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hval.le) (Valued.toNormedField.one_le_norm_iff.mpr hval.ge)
  have h1 : χ (a * ϖ ^ n) = 1 := hχ _ hnorm
  have ha' : a = (a * ϖ ^ n) * ϖ ^ (-n) := by rw [mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [ha', map_mul, h1, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]

theorem ofReal_norm_eq_qv_zpow {t : v.adicCompletion ℚ} {n : ℤ} (ht : Valued.v t = WithZero.exp n) :
    ((‖t‖ : ℝ) : ℂ) = qv v ^ n := by
  have h := ofReal_norm_eq_of_valued_eq v (t := t) (a := -n) (by rw [neg_neg]; exact ht)
  rw [h, qv, _root_.zpow_neg, inv_inv]

theorem apply_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) f) (x y z : v.adicCompletion ℚ) :
    f (antidiagonal3 v * upperUnipotent3 x y z) =
      f 1 * PP v χ ^ (e1 v x y z).log * QQ v χ ^ (e2 v x z).log := by
  obtain ⟨x', y', z', t, d, k, hk, htd, hg⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v (antidiagonal3 v * upperUnipotent3 x y z)
  have hdet : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det t).ne_zero
  rw [htd, Matrix.det_diagonal] at hdet
  have hd : ∀ i, d i ≠ 0 := fun i h0 => hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  set a : Fin 3 → (v.adicCompletion ℚ)ˣ := fun i => Units.mk0 (d i) (hd i) with ha
  have hta : t = diagonal3 v a :=
    Matrix.GeneralLinearGroup.ext fun i j => by simp only [htd, diagonal3_coe, ha, Units.val_mk0]
  obtain ⟨h2, h12, h012⟩ := iwasawa_invariants hk htd hg

  have hval : f (antidiagonal3 v * upperUnipotent3 x y z) = torusChar3 v χ a * halfModulus3 v a * f 1 := by
    rw [hg, hta, mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 hf,
      apply_diagonal3_mul_of_mem_principalSeries3 hf, ← one_mul k, hfK 1 k hk]

  set m₁ := (e1 v x y z).log with hm₁
  set m₂ := (e2 v x z).log with hm₂
  have he1 : e1 v x y z = WithZero.exp m₁ := (WithZero.exp_log (e1_ne_zero v x y z)).symm
  have he2 : e2 v x z = WithZero.exp m₂ := (WithZero.exp_log (e2_ne_zero v x z)).symm
  have hv2 : Valued.v ((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp m₂ := by
    rw [← he2]; exact h2
  have hv1 : Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (m₁ - m₂) := by
    have h := h12
    rw [h2, show max 1 (max (Valued.v y) (Valued.v (z - x * y))) = e1 v x y z from rfl, he1,
      show max 1 (max (Valued.v x) (Valued.v z)) = e2 v x z from rfl, he2] at h
    rw [WithZero.exp_sub]
    exact eq_div_of_mul_eq WithZero.exp_ne_zero h
  have hv0 : Valued.v ((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-m₁) := by
    have h := h012
    rw [mul_assoc, h12, show max 1 (max (Valued.v y) (Valued.v (z - x * y))) = e1 v x y z from rfl, he1] at h
    rw [WithZero.exp_neg]
    exact eq_inv_of_mul_eq_one_left h

  have hP0 := alpha_ne_zero v χ 0
  have hP1 := alpha_ne_zero v χ 1
  have hP2 := alpha_ne_zero v χ 2
  have hq := qv_ne_zero v
  rw [hval, torusChar3, Fin.prod_univ_three, halfModulus3, Complex.ofReal_div,
    char_eq_alpha_zpow (χ 0) (hχ 0) (a 0) (-m₁) hv0, char_eq_alpha_zpow (χ 1) (hχ 1) (a 1) (m₁ - m₂) hv1,
    char_eq_alpha_zpow (χ 2) (hχ 2) (a 2) m₂ hv2, ofReal_norm_eq_qv_zpow hv0, ofReal_norm_eq_qv_zpow hv2]
  simp only [PP, QQ, alpha] at *
  rw [neg_neg, neg_sub, zpow_sub₀ hP1, _root_.zpow_neg, _root_.zpow_neg, mul_zpow, mul_zpow, mul_zpow, mul_zpow,
    _root_.inv_zpow, _root_.inv_zpow, _root_.inv_zpow, _root_.inv_zpow]
  field_simp

end Value

end CSNV

end PartB

section PartC

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

namespace CSNV

section Haar1

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev borelAdicCompletionC : MeasurableSpace (v.adicCompletion ℚ) := borel (v.adicCompletion ℚ)

attribute [local instance] borelAdicCompletionC

theorem borelSpace_adicCompletionC : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩

attribute [local instance] borelSpace_adicCompletionC

def ball (k : ℤ) : Set (v.adicCompletion ℚ) := {t | Valued.v t ≤ WithZero.exp k}

theorem mem_ball_iff (k : ℤ) (t : v.adicCompletion ℚ) : t ∈ ball v k ↔ Valued.v t ≤ WithZero.exp k := Iff.rfl

theorem ball_mono {k l : ℤ} (h : k ≤ l) : ball v k ⊆ ball v l := fun _ ht =>
  le_trans ht (WithZero.exp_le_exp.mpr h)

theorem zero_mem_ball (k : ℤ) : (0 : v.adicCompletion ℚ) ∈ ball v k := by
  simp [ball]

theorem isClopen_ball (k : ℤ) : IsClopen (ball v k) := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero ((map_zero Valued.v).symm.trans ha).symm
  have hset : ball v k = (fun x => a⁻¹ * x) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
    ext x
    have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
      rw [ha]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
    simp only [ball, Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, map_inv₀, ← ha]
    rw [inv_mul_le_iff₀ hpos, mul_one]
  rw [hset]
  exact (isClopen_valued_le_one v).preimage (continuous_const.mul continuous_id)

theorem isCompact_ball (k : ℤ) : IsCompact (ball v k) := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero ((map_zero Valued.v).symm.trans ha).symm
  have hint : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers ℚ)))
  have hset : ball v k = (fun y => a * y) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext x
    have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
      rw [ha]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
    constructor
    · intro hx
      refine ⟨a⁻¹ * x, ?_, mul_inv_cancel_left₀ ha0 x⟩
      show Valued.v (a⁻¹ * x) ≤ 1
      rw [Valuation.map_mul, map_inv₀, inv_mul_le_iff₀ hpos, mul_one, ha]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      have hy' : Valued.v y ≤ 1 := hy
      show Valued.v (a * y) ≤ WithZero.exp k
      rw [Valuation.map_mul, ha]
      exact mul_le_of_le_one_right' hy'
  rw [hset]
  exact hint.image (continuous_const.mul continuous_id)

theorem measurableSet_ball (k : ℤ) : MeasurableSet (ball v k) := (isClopen_ball v k).isOpen.measurableSet

abbrev μv : Measure (v.adicCompletion ℚ) := Measure.addHaar

def V0 : ℝ := (μv v).real (ball v 0)

theorem V0_pos : 0 < V0 v := by
  rw [V0, measureReal_def]
  refine ENNReal.toReal_pos ?_ (isCompact_ball v 0).measure_lt_top.ne
  exact ((isClopen_ball v 0).isOpen.measure_pos (μv v) ⟨_, zero_mem_ball v 0⟩).ne'

theorem measure_ball_lt_top (k : ℤ) : μv v (ball v k) < ⊤ := (isCompact_ball v k).measure_lt_top

theorem measure_ball_succ (k : ℤ) :
    μv v (ball v (k + 1)) = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ENNReal) * μv v (ball v k) := by
  classical
  obtain ⟨X, hX, hX', hcard⟩ := exists_finset_ball_representatives v (-(k + 1)) (-k) (by omega)
  simp only [neg_neg] at hX hX'
  have hcard' : X.card = Nat.card (𝓞 ℚ ⧸ v.asIdeal) := by
    rw [hcard, show (-k - -(k + 1)).toNat = 1 by omega, pow_one]
  have hcover : ball v (k + 1) = ⋃ r ∈ X, (fun t => -r + t) ⁻¹' ball v k := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
    constructor
    · intro ht
      obtain ⟨r, ⟨hr, hclose⟩, -⟩ := hX' t ht
      refine ⟨r, hr, ?_⟩
      show Valued.v (-r + t) ≤ WithZero.exp k
      rwa [neg_add_eq_sub]
    · rintro ⟨r, hr, hu⟩
      have hu' : Valued.v (-r + t) ≤ WithZero.exp k := hu
      have h1 : t = r + (-r + t) := by ring
      rw [mem_ball_iff, h1]
      refine (Valuation.map_add _ _ _).trans (max_le (hX r hr) (le_trans hu' (WithZero.exp_le_exp.mpr (by omega))))
  have hdisj : (X : Set (v.adicCompletion ℚ)).PairwiseDisjoint fun r => (fun t => -r + t) ⁻¹' ball v k := by
    intro r hr r' hr' hne
    refine Set.disjoint_left.mpr ?_
    intro t ht ht'
    have ht1 : Valued.v (-r + t) ≤ WithZero.exp k := ht
    have ht2 : Valued.v (-r' + t) ≤ WithZero.exp k := ht'
    have htb : Valued.v t ≤ WithZero.exp (k + 1) := by
      have h1 : t = r + (-r + t) := by ring
      rw [h1]
      exact (Valuation.map_add _ _ _).trans (max_le (hX r hr) (le_trans ht1 (WithZero.exp_le_exp.mpr (by omega))))
    obtain ⟨r₀, -, huniq⟩ := hX' t htb
    have h1 : r = r₀ := huniq r ⟨hr, by rwa [← neg_add_eq_sub]⟩
    have h2 : r' = r₀ := huniq r' ⟨hr', by rwa [← neg_add_eq_sub]⟩
    exact hne (h1.trans h2.symm)
  rw [hcover, measure_biUnion_finset hdisj (fun r _ => measurable_const_add (-r) (measurableSet_ball v k))]
  simp only [measure_preimage_add]
  rw [Finset.sum_const, hcard', nsmul_eq_mul]

theorem real_ball_succ (k : ℤ) :
    (μv v).real (ball v (k + 1)) = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) * (μv v).real (ball v k) := by
  rw [measureReal_def, measureReal_def, measure_ball_succ, ENNReal.toReal_mul]
  simp

theorem real_ball_one : (μv v).real (ball v 1) = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) * V0 v := by
  rw [V0, show (1 : ℤ) = 0 + 1 by ring, real_ball_succ]

theorem real_preimage_add (a : v.adicCompletion ℚ) (s : Set (v.adicCompletion ℚ)) :
    (μv v).real ((fun t => a + t) ⁻¹' s) = (μv v).real s := by
  simp only [measureReal_def, measure_preimage_add]

variable {v}

theorem integral_indicator_mul_addChar_eq_zero (ψ : AddChar (v.adicCompletion ℚ) ℂ) {a : v.adicCompletion ℚ}
    (ha : ψ a ≠ 1) {S : Set (v.adicCompletion ℚ)} (hS : ∀ t, t - a ∈ S ↔ t ∈ S) {G : v.adicCompletion ℚ → ℂ}
    (hG : ∀ t ∈ S, G (t - a) = G t) :
    ∫ t, S.indicator (fun t => ψ (-t) * G t) t ∂(μv v) = 0 := by
  set J := ∫ t, S.indicator (fun t => ψ (-t) * G t) t ∂(μv v) with hJ
  have hshift := integral_add_right_eq_self (μ := μv v) (S.indicator (fun t => ψ (-t) * G t)) (-a)
  have hpt : ∀ t, S.indicator (fun t => ψ (-t) * G t) (t + -a) = ψ a * S.indicator (fun t => ψ (-t) * G t) t := by
    intro t
    rw [← sub_eq_add_neg]
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ((hS t).mpr ht), Set.indicator_of_mem ht, hG t ht, neg_sub, sub_eq_add_neg,
        AddChar.map_add_eq_mul]
      ring
    · rw [Set.indicator_of_notMem (fun h => ht ((hS t).mp h)), Set.indicator_of_notMem ht, mul_zero]
  simp_rw [hpt] at hshift
  rw [integral_const_mul] at hshift
  have h : (ψ a - 1) * J = 0 := by rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha)

theorem integral_indicator_ball_addChar_eq_zero (ψ : AddChar (v.adicCompletion ℚ) ℂ) {a : v.adicCompletion ℚ}
    (ha : ψ a ≠ 1) {k : ℤ} (hak : Valued.v a ≤ WithZero.exp k) :
    ∫ t, (ball v k).indicator (fun t => ψ (-t)) t ∂(μv v) = 0 := by
  have h := integral_indicator_mul_addChar_eq_zero ψ ha (S := ball v k) (G := fun _ => (1 : ℂ)) ?_ (fun _ _ => rfl)
  · simpa using h
  · intro t
    simp only [mem_ball_iff]
    constructor
    · intro ht
      have : t = (t - a) + a := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le ht hak)
    · intro ht
      exact (Valuation.map_sub _ _ _).trans (max_le ht hak)

theorem integral_indicator_ball_zero_addChar (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1) :
    ∫ t, (ball v 0).indicator (fun t => ψ (-t)) t ∂(μv v) = (V0 v : ℂ) := by
  have hpt : (ball v 0).indicator (fun t => ψ (-t)) = (ball v 0).indicator (fun _ => (1 : ℂ)) := by
    funext t
    by_cases ht : t ∈ ball v 0
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      refine hψ0 _ ?_
      rw [Valuation.map_neg]
      simpa [ball] using ht
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  rw [hpt, integral_indicator_const _ (measurableSet_ball v 0), V0]
  simp [Complex.real_smul]

variable (v)

theorem measurePreserving_mul_left {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) :
    MeasurePreserving (fun t => u * t) (μv v) (μv v) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact zero_ne_one hu
  set U : (v.adicCompletion ℚ)ˣ := Units.mk0 u hu0 with hU
  set e : v.adicCompletion ℚ ≃+ v.adicCompletion ℚ := DistribMulAction.toAddEquiv (v.adicCompletion ℚ) U with he
  have hecoe : (e : v.adicCompletion ℚ → v.adicCompletion ℚ) = fun t => u * t := by
    funext t; rfl
  have hcont : Continuous e := by rw [hecoe]; exact continuous_const.mul continuous_id
  have hcont' : Continuous e.symm := by
    have : (e.symm : v.adicCompletion ℚ → v.adicCompletion ℚ) = fun t => u⁻¹ * t := by
      funext t
      show (U⁻¹ : (v.adicCompletion ℚ)ˣ) • t = u⁻¹ * t
      rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul]
    rw [this]; exact continuous_const.mul continuous_id
  let eh : v.adicCompletion ℚ ≃ₜ v.adicCompletion ℚ :=
    { e.toEquiv with continuous_toFun := hcont, continuous_invFun := hcont' }
  haveI : (Measure.map e (μv v)).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map (μv v) e hcont hcont'
  haveI : (Measure.map e (μv v)).Regular := Measure.Regular.map eh
  have heq := Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.map e (μv v)) (μv v)

  set c := (Measure.map e (μv v)).addHaarScalarFactor (μv v) with hc
  have hpre : e ⁻¹' ball v 0 = ball v 0 := by
    ext t
    simp only [Set.mem_preimage, mem_ball_iff, hecoe, Valuation.map_mul, hu, one_mul]
  have hB : Measure.map e (μv v) (ball v 0) = μv v (ball v 0) := by
    rw [Measure.map_apply hcont.measurable (measurableSet_ball v 0), hpre]
  have hc1 : c = 1 := by
    have h := congrArg (fun m : Measure (v.adicCompletion ℚ) => m (ball v 0)) heq
    simp only [Measure.smul_apply, hB] at h
    have hne : μv v (ball v 0) ≠ 0 :=
      ((isClopen_ball v 0).isOpen.measure_pos (μv v) ⟨_, zero_mem_ball v 0⟩).ne'
    have hfin : μv v (ball v 0) ≠ ⊤ := (measure_ball_lt_top v 0).ne
    rw [ENNReal.smul_def, smul_eq_mul] at h
    have h' : (c : ENNReal) * μv v (ball v 0) = 1 * μv v (ball v 0) := by rw [one_mul]; exact h.symm
    exact ENNReal.coe_eq_one.mp ((ENNReal.mul_left_inj hne hfin).mp h')
  rw [hc1, one_smul] at heq
  exact ⟨by rw [← hecoe]; exact hcont.measurable, by rw [← hecoe]; exact heq⟩

end Haar1

end CSNV

end PartC

section PartD

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

namespace CSNV

section Exponents

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem max_zero_left' (a : WithZero (Multiplicative ℤ)) : max 0 a = a := max_eq_right zero_le'

variable {v}

theorem max_valued_sub_eq {y z w : v.adicCompletion ℚ} (h : Valued.v w ≤ Valued.v y) :
    max (Valued.v y) (Valued.v (z - w)) = max (Valued.v y) (Valued.v z) := by
  apply le_antisymm
  · exact max_le (le_max_left _ _)
      ((Valuation.map_sub _ _ _).trans (max_le (le_max_right _ _) (h.trans (le_max_left _ _))))
  · apply max_le (le_max_left _ _)
    have hz : Valued.v z ≤ max (Valued.v (z - w)) (Valued.v w) := by
      have e : z = (z - w) + w := by ring
      calc Valued.v z = Valued.v ((z - w) + w) := by rw [← e]
        _ ≤ max (Valued.v (z - w)) (Valued.v w) := Valuation.map_add _ _ _
    exact hz.trans (max_le (le_max_right _ _) (h.trans (le_max_left _ _)))

variable (v)

theorem e2_of_valued_le_one {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (z : v.adicCompletion ℚ) :
    e2 v x z = max 1 (Valued.v z) := by
  unfold e2; rw [← max_assoc, max_eq_left hx]

theorem e2_zero (z : v.adicCompletion ℚ) : e2 v 0 z = max 1 (Valued.v z) :=
  e2_of_valued_le_one v (by rw [map_zero]; exact zero_le') z

theorem e1_of_valued_le_one {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (y z : v.adicCompletion ℚ) :
    e1 v x y z = max 1 (max (Valued.v y) (Valued.v z)) := by
  unfold e1
  rw [max_valued_sub_eq]
  rw [map_mul]
  exact mul_le_of_le_one_left' hx

theorem e1_zero_mid (x z : v.adicCompletion ℚ) : e1 v x 0 z = max 1 (Valued.v z) := by
  unfold e1; rw [mul_zero, sub_zero, map_zero, max_zero_left']

theorem e1_translate {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) (x z : v.adicCompletion ℚ) :
    e1 v x y (z + x * y) = max 1 (Valued.v z) := by
  unfold e1; rw [add_sub_cancel_right, ← max_assoc, max_eq_left hy]

theorem e2_translate {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) (x z : v.adicCompletion ℚ) :
    e2 v x (z + x * y) = e2 v x z := by
  unfold e2
  rw [show z + x * y = z - (-(x * y)) by ring, max_valued_sub_eq]
  rw [Valuation.map_neg, map_mul]
  exact mul_le_of_le_one_right' hy

theorem e2_unit {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x z : v.adicCompletion ℚ) :
    e2 v (u * x) (u * z) = e2 v x z := by
  unfold e2; rw [map_mul, map_mul, hu, one_mul, one_mul]

theorem e2_unit_z {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x z : v.adicCompletion ℚ) :
    e2 v x (u * z) = e2 v x z := by
  unfold e2; rw [map_mul, hu, one_mul]

theorem e1_unit_x {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x y z : v.adicCompletion ℚ) :
    e1 v (u * x) y (u * z) = e1 v x y z := by
  unfold e1; rw [show u * z - u * x * y = u * (z - x * y) by ring, map_mul, hu, one_mul]

theorem e1_unit_y {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x y z : v.adicCompletion ℚ) :
    e1 v x (u * y) (u * z) = e1 v x y z := by
  unfold e1; rw [show u * z - x * (u * y) = u * (z - x * y) by ring, map_mul, map_mul, hu, one_mul, one_mul]

theorem e2_large {x z : v.adicCompletion ℚ} (h1 : 1 ≤ Valued.v z) (hx : Valued.v x ≤ Valued.v z) :
    e2 v x z = Valued.v z := by
  unfold e2; rw [max_eq_right hx, max_eq_right h1]

theorem e1_large {x y z : v.adicCompletion ℚ} (h1 : 1 ≤ Valued.v z) (hy : Valued.v y ≤ Valued.v z)
    (hxy : Valued.v (x * y) < Valued.v z) : e1 v x y z = Valued.v z := by
  unfold e1; rw [Valuation.map_sub_eq_of_lt_left _ hxy, max_eq_right hy, max_eq_right h1]

theorem e1_small {x y z : v.adicCompletion ℚ} (h : Valued.v z < Valued.v (x * y)) :
    e1 v x y z = max 1 (max (Valued.v y) (Valued.v (x * y))) := by
  unfold e1; rw [Valuation.map_sub_eq_of_lt_right _ h]

theorem exp_add_one_le_of_not_le {e : WithZero (Multiplicative ℤ)} {n : ℤ} (h : ¬ e ≤ WithZero.exp n) :
    WithZero.exp (n + 1) ≤ e := by
  have he : e ≠ 0 := by
    rintro rfl
    exact h zero_le'
  rw [← WithZero.exp_log he] at h ⊢
  rw [WithZero.exp_le_exp] at h ⊢
  omega

end Exponents

section ZIntegral

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] borelAdicCompletionC borelSpace_adicCompletionC

def Fw (f : LocalGL3 v → ℂ) (x y z : v.adicCompletion ℚ) : ℂ := f (antidiagonal3 v * upperUnipotent3 x y z)

def Iz (f : LocalGL3 v → ℂ) (c : ℤ) (x y : v.adicCompletion ℚ) : ℂ :=
  ∫ z, (ball v (2 * c)).indicator (Fw v f x y) z ∂(μv v)

variable {v}

section Formula

variable {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
  (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
  {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
  (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) f)

include hχ hf hfK

theorem Fw_eq (x y z : v.adicCompletion ℚ) :
    Fw v f x y z = f 1 * PP v χ ^ (e1 v x y z).log * QQ v χ ^ (e2 v x z).log :=
  apply_antidiagonal3_mul_upperUnipotent3 χ hχ hf hfK x y z

theorem Fw_of_valued_le_one {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (y z : v.adicCompletion ℚ) :
    Fw v f x y z = Fw v f 0 y z := by
  rw [Fw_eq hχ hf hfK, Fw_eq hχ hf hfK, e1_of_valued_le_one v hx, e2_of_valued_le_one v hx,
    e1_of_valued_le_one v (by rw [map_zero]; exact zero_le'), e2_zero]

theorem Fw_translate {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) (x z : v.adicCompletion ℚ) :
    Fw v f x y (z + x * y) = Fw v f x 0 z := by
  rw [Fw_eq hχ hf hfK, Fw_eq hχ hf hfK, e1_translate v hy, e2_translate v hy, e1_zero_mid]

theorem Fw_unit_x {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x y z : v.adicCompletion ℚ) :
    Fw v f (u * x) y (u * z) = Fw v f x y z := by
  rw [Fw_eq hχ hf hfK, Fw_eq hχ hf hfK, e1_unit_x v hu, e2_unit v hu]

theorem Fw_unit_y {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x y z : v.adicCompletion ℚ) :
    Fw v f x (u * y) (u * z) = Fw v f x y z := by
  rw [Fw_eq hχ hf hfK, Fw_eq hχ hf hfK, e1_unit_y v hu, e2_unit_z v hu]

theorem Iz_of_valued_le_one (c : ℤ) {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (y : v.adicCompletion ℚ) :
    Iz v f c x y = Iz v f c 0 y := by
  unfold Iz
  congr 1
  funext z
  simp only [Set.indicator]
  split_ifs <;> simp [Fw_of_valued_le_one hχ hf hfK hx]

theorem Iz_of_valued_mid_le_one (c : ℤ) (x : v.adicCompletion ℚ) {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1)
    (hxy : Valued.v (x * y) ≤ WithZero.exp (2 * c)) : Iz v f c x y = Iz v f c x 0 := by
  unfold Iz
  rw [← integral_add_right_eq_self (μ := μv v) ((ball v (2 * c)).indicator (Fw v f x y)) (x * y)]
  congr 1
  funext z
  have hmem : z + x * y ∈ ball v (2 * c) ↔ z ∈ ball v (2 * c) := by
    simp only [mem_ball_iff]
    constructor
    · intro h
      have e : z = (z + x * y) - x * y := by ring
      calc Valued.v z = Valued.v ((z + x * y) - x * y) := by rw [← e]
        _ ≤ _ := (Valuation.map_sub _ _ _).trans (max_le h hxy)
    · intro h
      exact (Valuation.map_add _ _ _).trans (max_le h hxy)
  by_cases hz : z ∈ ball v (2 * c)
  · rw [Set.indicator_of_mem (hmem.mpr hz), Set.indicator_of_mem hz, Fw_translate hχ hf hfK hy]
  · rw [Set.indicator_of_notMem (fun h => hz (hmem.mp h)), Set.indicator_of_notMem hz]

theorem Iz_unit_x (c : ℤ) {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x y : v.adicCompletion ℚ) :
    Iz v f c (u * x) y = Iz v f c x y := by
  unfold Iz
  rw [← (measurePreserving_mul_left v hu).integral_comp ?emb ((ball v (2 * c)).indicator (Fw v f (u * x) y))]
  case emb =>
    have hu0 : u ≠ 0 := by
      rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
    exact (Homeomorph.mulLeft₀ u hu0).measurableEmbedding
  congr 1
  funext z
  have hmem : u * z ∈ ball v (2 * c) ↔ z ∈ ball v (2 * c) := by
    simp only [mem_ball_iff, map_mul, hu, one_mul]
  by_cases hz : z ∈ ball v (2 * c)
  · rw [Set.indicator_of_mem (hmem.mpr hz), Set.indicator_of_mem hz, Fw_unit_x hχ hf hfK hu]
  · rw [Set.indicator_of_notMem (fun h => hz (hmem.mp h)), Set.indicator_of_notMem hz]

theorem Iz_unit_y (c : ℤ) {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) (x y : v.adicCompletion ℚ) :
    Iz v f c x (u * y) = Iz v f c x y := by
  unfold Iz
  rw [← (measurePreserving_mul_left v hu).integral_comp ?emb ((ball v (2 * c)).indicator (Fw v f x (u * y)))]
  case emb =>
    have hu0 : u ≠ 0 := by
      rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu
    exact (Homeomorph.mulLeft₀ u hu0).measurableEmbedding
  congr 1
  funext z
  have hmem : u * z ∈ ball v (2 * c) ↔ z ∈ ball v (2 * c) := by
    simp only [mem_ball_iff, map_mul, hu, one_mul]
  by_cases hz : z ∈ ball v (2 * c)
  · rw [Set.indicator_of_mem (hmem.mpr hz), Set.indicator_of_mem hz, Fw_unit_y hχ hf hfK hu]
  · rw [Set.indicator_of_notMem (fun h => hz (hmem.mp h)), Set.indicator_of_notMem hz]

end Formula

end ZIntegral

section Radial

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] borelAdicCompletionC borelSpace_adicCompletionC

structure IsRadial (g : v.adicCompletion ℚ → ℂ) : Prop where
  eq_zero : ∀ y, Valued.v y ≤ 1 → g y = g 0
  unit : ∀ u y, Valued.v u = 1 → g (u * y) = g y

variable {v}

theorem IsRadial.eq_of_valued_eq {g : v.adicCompletion ℚ → ℂ} (hg : IsRadial v g) {y y' : v.adicCompletion ℚ}
    (hy : y ≠ 0) (h : Valued.v y' = Valued.v y) : g y' = g y := by
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hu : Valued.v (y' * y⁻¹) = 1 := by
    rw [map_mul, map_inv₀, h, mul_inv_cancel₀ hvy]
  have := hg.unit (y' * y⁻¹) y hu
  rwa [mul_assoc, inv_mul_cancel₀ hy, mul_one] at this

theorem IsRadial.continuous {g : v.adicCompletion ℚ → ℂ} (hg : IsRadial v g) : Continuous g := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).mpr fun y₀ => ?_)
  by_cases hy₀ : Valued.v y₀ ≤ 1
  · have hopen : IsOpen (ball v 0) := (isClopen_ball v 0).isOpen
    have hmem : y₀ ∈ ball v 0 := by simpa [mem_ball_iff] using hy₀
    filter_upwards [hopen.mem_nhds hmem] with y hy
    have hy' : Valued.v y ≤ 1 := by simpa [mem_ball_iff] using hy
    rw [hg.eq_zero y hy', hg.eq_zero y₀ hy₀]
  · have hne : y₀ ≠ 0 := by
      rintro rfl; rw [map_zero] at hy₀; exact hy₀ zero_le'
    filter_upwards [eventually_valued_eq v hne] with y hy
    exact hg.eq_of_valued_eq hne hy

theorem IsRadial.sub {g : v.adicCompletion ℚ → ℂ} (hg : IsRadial v g) {y a : v.adicCompletion ℚ}
    (h : Valued.v a < Valued.v y) : g (y - a) = g y := by
  have hy : y ≠ 0 := by
    rintro rfl; rw [map_zero] at h; exact not_lt_of_ge zero_le' h
  exact hg.eq_of_valued_eq hy (Valuation.map_sub_eq_of_lt_left _ h)

theorem integrable_indicator_of_continuous {φ : v.adicCompletion ℚ → ℂ} (hφ : Continuous φ)
    {S : Set (v.adicCompletion ℚ)} (hS : MeasurableSet S) {k : ℤ} (hSk : S ⊆ ball v k) :
    Integrable (S.indicator φ) (μv v) :=
  (integrable_indicator_iff hS).mpr ((hφ.continuousOn.integrableOn_compact (isCompact_ball v k)).mono_set hSk)

theorem integral_ball_addChar_mul_radial (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1)
    {a : v.adicCompletion ℚ} (ha1 : Valued.v a ≤ WithZero.exp 1) (ha : ψ a ≠ 1)
    {g : v.adicCompletion ℚ → ℂ} (hg : IsRadial v g) {c : ℤ} (hc : 1 ≤ c)
    {y₁ : v.adicCompletion ℚ} (hy₁ : Valued.v y₁ = WithZero.exp 1) :
    ∫ y, (ball v c).indicator (fun y => ψ (-y) * g y) y ∂(μv v) = (V0 v : ℂ) * (g 0 - g y₁) := by
  have hψc : Continuous ψ :=
    continuous_addChar_of_eq_one_on_ball v ψ 0 (fun x hx => hψ0 x (by simpa using hx))
  have hcont : Continuous fun y => ψ (-y) * g y := (hψc.comp continuous_neg).mul hg.continuous
  have h01 : ball v 0 ⊆ ball v 1 := ball_mono v (by norm_num)
  have h1c : ball v 1 ⊆ ball v c := ball_mono v hc

  have hsplit : (ball v c).indicator (fun y => ψ (-y) * g y) =
      (ball v 0).indicator (fun _ => g 0) +
      (fun y => (ball v 1 \ ball v 0).indicator (fun y => ψ (-y)) y * g y₁) +
      (ball v c \ ball v 1).indicator (fun y => ψ (-y) * g y) := by
    funext y
    simp only [Pi.add_apply]
    by_cases h0 : y ∈ ball v 0
    · have hy : Valued.v y ≤ 1 := by simpa [mem_ball_iff] using h0
      have hn1 : y ∉ ball v 1 \ ball v 0 := fun h => h.2 h0
      have hnc : y ∉ ball v c \ ball v 1 := fun h => h.2 (h01 h0)
      rw [Set.indicator_of_mem (s := ball v c) (h1c (h01 h0)), Set.indicator_of_mem (s := ball v 0) h0,
        Set.indicator_of_notMem (s := ball v 1 \ ball v 0) hn1, Set.indicator_of_notMem (s := ball v c \ ball v 1) hnc,
        hg.eq_zero y hy, hψ0 (-y) (by rwa [Valuation.map_neg])]
      ring
    · rw [Set.indicator_of_notMem (s := ball v 0) h0]
      by_cases h1 : y ∈ ball v 1
      · have hy : Valued.v y = WithZero.exp 1 := by
          refine le_antisymm h1 ?_
          have := exp_add_one_le_of_not_le (e := Valued.v y) (n := 0) (by simpa [mem_ball_iff] using h0)
          simpa using this
        have hy₁ne : y₁ ≠ 0 := by
          rintro rfl; rw [map_zero] at hy₁; exact WithZero.exp_ne_zero hy₁.symm
        have hm1 : y ∈ ball v 1 \ ball v 0 := ⟨h1, h0⟩
        have hnc : y ∉ ball v c \ ball v 1 := fun h => h.2 h1
        rw [Set.indicator_of_mem (s := ball v c) (h1c h1), Set.indicator_of_mem (s := ball v 1 \ ball v 0) hm1,
          Set.indicator_of_notMem (s := ball v c \ ball v 1) hnc, hg.eq_of_valued_eq hy₁ne (by rw [hy, hy₁])]
        ring
      · have hn1 : y ∉ ball v 1 \ ball v 0 := fun h => h1 h.1
        rw [Set.indicator_of_notMem (s := ball v 1 \ ball v 0) hn1]
        by_cases hc' : y ∈ ball v c
        · have hmc : y ∈ ball v c \ ball v 1 := ⟨hc', h1⟩
          rw [Set.indicator_of_mem (s := ball v c) hc', Set.indicator_of_mem (s := ball v c \ ball v 1) hmc]
          ring
        · have hnc : y ∉ ball v c \ ball v 1 := fun h => hc' h.1
          rw [Set.indicator_of_notMem (s := ball v c) hc', Set.indicator_of_notMem (s := ball v c \ ball v 1) hnc]
          ring

  have hi0 : Integrable ((ball v 0).indicator fun _ => g 0) (μv v) :=
    integrable_indicator_of_continuous continuous_const (measurableSet_ball v 0) (subset_refl _)
  have hishell : Integrable ((ball v 1 \ ball v 0).indicator fun y => ψ (-y)) (μv v) :=
    integrable_indicator_of_continuous (hψc.comp continuous_neg)
      ((measurableSet_ball v 1).diff (measurableSet_ball v 0)) Set.diff_subset
  have hi1 : Integrable (fun y => (ball v 1 \ ball v 0).indicator (fun y => ψ (-y)) y * g y₁) (μv v) :=
    hishell.mul_const _
  have hi2 : Integrable ((ball v c \ ball v 1).indicator fun y => ψ (-y) * g y) (μv v) :=
    integrable_indicator_of_continuous hcont ((measurableSet_ball v c).diff (measurableSet_ball v 1)) Set.diff_subset
  rw [hsplit, integral_add' (hi0.add hi1) hi2, integral_add' hi0 hi1]

  have hp0 : ∫ y, (ball v 0).indicator (fun _ => g 0) y ∂(μv v) = (V0 v : ℂ) * g 0 := by
    rw [integral_indicator_const _ (measurableSet_ball v 0), V0, Complex.real_smul]

  have hshell : (ball v 1 \ ball v 0).indicator (fun y => ψ (-y)) =
      (ball v 1).indicator (fun y => ψ (-y)) - (ball v 0).indicator (fun y => ψ (-y)) := by
    funext y
    simp only [Pi.sub_apply]
    by_cases h0 : y ∈ ball v 0
    · rw [Set.indicator_of_notMem (s := ball v 1 \ ball v 0) (fun h => h.2 h0),
        Set.indicator_of_mem (s := ball v 1) (h01 h0), Set.indicator_of_mem (s := ball v 0) h0, sub_self]
    · rw [Set.indicator_of_notMem (s := ball v 0) h0, sub_zero]
      by_cases h1 : y ∈ ball v 1
      · rw [Set.indicator_of_mem (s := ball v 1 \ ball v 0) ⟨h1, h0⟩, Set.indicator_of_mem (s := ball v 1) h1]
      · rw [Set.indicator_of_notMem (s := ball v 1 \ ball v 0) (fun h => h1 h.1),
          Set.indicator_of_notMem (s := ball v 1) h1]
  have hneg : ψ (-a) ≠ 1 := by
    intro h
    apply ha
    have := AddChar.map_add_eq_mul ψ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, mul_one] at this
    exact this.symm
  have hp1 : ∫ y, (ball v 1 \ ball v 0).indicator (fun y => ψ (-y)) y * g y₁ ∂(μv v) = -(V0 v : ℂ) * g y₁ := by
    rw [integral_mul_const, hshell, integral_sub'
      (integrable_indicator_of_continuous (φ := fun y => ψ (-y)) (hψc.comp continuous_neg) (measurableSet_ball v 1)
        (subset_refl _))
      (integrable_indicator_of_continuous (φ := fun y => ψ (-y)) (hψc.comp continuous_neg) (measurableSet_ball v 0)
        (subset_refl _)),
      integral_indicator_ball_addChar_eq_zero ψ hneg (k := 1) (by rwa [Valuation.map_neg]),
      integral_indicator_ball_zero_addChar ψ hψ0]
    ring

  have hp2 : ∫ y, (ball v c \ ball v 1).indicator (fun y => ψ (-y) * g y) y ∂(μv v) = 0 := by
    refine integral_indicator_mul_addChar_eq_zero ψ hneg (S := ball v c \ ball v 1) (G := g) ?_ ?_
    · intro t
      have key : ∀ s : v.adicCompletion ℚ, s ∈ ball v c \ ball v 1 → Valued.v (-a) < Valued.v s := by
        rintro s ⟨-, hs1⟩
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt ha1 (lt_of_lt_of_le (by rw [WithZero.exp_lt_exp]; norm_num)
          (exp_add_one_le_of_not_le (n := 1) (by simpa [mem_ball_iff] using hs1)))
      constructor
      · intro h
        have hlt := key _ h
        have heq : Valued.v t = Valued.v (t - -a) := by
          have e : t = (t - -a) + -a := by ring
          conv_lhs => rw [e]
          exact Valuation.map_add_eq_of_lt_left _ hlt
        simp only [Set.mem_diff, mem_ball_iff] at h ⊢
        rw [heq]; exact h
      · intro h
        have hlt := key _ h
        have heq : Valued.v (t - -a) = Valued.v t := Valuation.map_sub_eq_of_lt_left _ hlt
        simp only [Set.mem_diff, mem_ball_iff] at h ⊢
        rw [heq]; exact h
    · rintro t ⟨-, ht1⟩
      apply hg.sub
      rw [Valuation.map_neg]
      exact lt_of_le_of_lt ha1 (lt_of_lt_of_le (by rw [WithZero.exp_lt_exp]; norm_num)
        (exp_add_one_le_of_not_le (n := 1) (by simpa [mem_ball_iff] using ht1)))
  simp only [hp0, hp2]
  rw [show (∫ a, (fun y => (ball v 1 \ ball v 0).indicator (fun y => ψ (-y)) y * g y₁) a ∂(μv v)) = -(V0 v : ℂ) * g y₁
    from hp1]
  ring

end Radial

end CSNV

end PartD

section PartE

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

namespace CSNV

section Link

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] borelAdicCompletionC borelSpace_adicCompletionC

def Hy (ψ : AddChar (v.adicCompletion ℚ) ℂ) (f : LocalGL3 v → ℂ) (c : ℤ) (x : v.adicCompletion ℚ) : ℂ :=
  ∫ y, (ball v c).indicator (fun y => ψ (-y) * Iz v f c x y) y ∂(μv v)

def Dx (ψ : AddChar (v.adicCompletion ℚ) ℂ) (f : LocalGL3 v → ℂ) (c : ℤ) : ℂ :=
  ∫ x, (ball v c).indicator (fun x => ψ (-x) * Hy v ψ f c x) x ∂(μv v)

variable {v}

theorem continuous_Fw23 {f : LocalGL3 v → ℂ} (hf : Continuous f) (x : v.adicCompletion ℚ) :
    Continuous fun w : v.adicCompletion ℚ × v.adicCompletion ℚ => Fw v f x w.1 w.2 := by
  have h1 : Continuous fun w : v.adicCompletion ℚ × v.adicCompletion ℚ =>
      ((x, w) : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous fun w : v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (antidiagonal3 v * upperUnipotent3 x w.1 w.2 : LocalGL3 v) :=
    continuous_const.mul ((continuous_upperUnipotent3_coords v).comp h1)
  exact hf.comp h2

theorem continuous_Fw3 {f : LocalGL3 v → ℂ} (hf : Continuous f) (x y : v.adicCompletion ℚ) :
    Continuous fun z : v.adicCompletion ℚ => Fw v f x y z := by
  have h1 : Continuous fun z : v.adicCompletion ℚ => ((y, z) : v.adicCompletion ℚ × v.adicCompletion ℚ) :=
    continuous_const.prodMk continuous_id
  exact ((continuous_Fw23 hf x).comp h1).congr (fun z => by simp only [Function.comp_apply])

theorem integrable_indicator_Fw {f : LocalGL3 v → ℂ} (hf : Continuous f) (c : ℤ) (x y : v.adicCompletion ℚ) :
    Integrable ((ball v (2 * c)).indicator (Fw v f x y)) (μv v) :=
  integrable_indicator_of_continuous (continuous_Fw3 hf x y) (measurableSet_ball v (2 * c)) (subset_refl _)

def Kfun (ψ : AddChar (v.adicCompletion ℚ) ℂ) (f : LocalGL3 v → ℂ) (c : ℤ) (x : v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ :=
  (ball v c ×ˢ ball v (2 * c)).indicator (fun w => ψ (-w.1) * Fw v f x w.1 w.2)

theorem Kfun_apply (ψ : AddChar (v.adicCompletion ℚ) ℂ) (f : LocalGL3 v → ℂ) (c : ℤ) (x y z : v.adicCompletion ℚ) :
    Kfun ψ f c x (y, z) = (ball v c).indicator (fun y => ψ (-y)) y * (ball v (2 * c)).indicator (Fw v f x y) z := by
  unfold Kfun
  by_cases hy : y ∈ ball v c
  · by_cases hz : z ∈ ball v (2 * c)
    · rw [Set.indicator_of_mem (show (y, z) ∈ ball v c ×ˢ ball v (2 * c) from Set.mk_mem_prod hy hz),
        Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (show (y, z) ∉ ball v c ×ˢ ball v (2 * c) from fun h => hz h.2),
        Set.indicator_of_notMem hz, mul_zero]
  · rw [Set.indicator_of_notMem (show (y, z) ∉ ball v c ×ˢ ball v (2 * c) from fun h => hy h.1),
      Set.indicator_of_notMem hy, zero_mul]

theorem detectorIntegrand_eq (ψ : AddChar (v.adicCompletion ℚ) ℂ) (f : LocalGL3 v → ℂ) (c : ℤ) :
    detectorIntegrand v ψ c f = fun p => (ball v c).indicator (fun x => ψ (-x)) p.1 * Kfun ψ f c p.1 p.2 := by
  funext p
  obtain ⟨x, y, z⟩ := p
  show detectorIntegrand v ψ c f (x, y, z) = (ball v c).indicator (fun x => ψ (-x)) x * Kfun ψ f c x (y, z)
  rw [Kfun_apply]
  by_cases hx : x ∈ ball v c
  · by_cases hy : y ∈ ball v c
    · by_cases hz : z ∈ ball v (2 * c)
      · have hp : (x, y, z) ∈ unipotentBall v c := ⟨hx, hy, hz⟩
        rw [detectorIntegrand, Set.indicator_of_mem hp, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hz, Fw, neg_add, AddChar.map_add_eq_mul]
        ring
      · have hp : (x, y, z) ∉ unipotentBall v c := fun h => hz h.2.2
        rw [detectorIntegrand, Set.indicator_of_notMem hp, Set.indicator_of_notMem hz, mul_zero, mul_zero]
    · have hp : (x, y, z) ∉ unipotentBall v c := fun h => hy h.2.1
      rw [detectorIntegrand, Set.indicator_of_notMem hp, Set.indicator_of_notMem hy, zero_mul, mul_zero]
  · have hp : (x, y, z) ∉ unipotentBall v c := fun h => hx h.1
    rw [detectorIntegrand, Set.indicator_of_notMem hp, Set.indicator_of_notMem hx, zero_mul]

theorem integrable_Kfun {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψc : Continuous ψ) {f : LocalGL3 v → ℂ}
    (hf : Continuous f) (c : ℤ) (x : v.adicCompletion ℚ) : Integrable (Kfun ψ f c x) ((μv v).prod (μv v)) := by
  unfold Kfun
  exact (integrable_indicator_iff ((measurableSet_ball v c).prod (measurableSet_ball v (2 * c)))).mpr
    ((((hψc.comp (continuous_fst.neg)).mul (continuous_Fw23 hf x)).continuousOn.integrableOn_compact
      ((isCompact_ball v c).prod (isCompact_ball v (2 * c)))))

theorem integral_Kfun {ψ : AddChar (v.adicCompletion ℚ) ℂ} (hψc : Continuous ψ) {f : LocalGL3 v → ℂ}
    (hf : Continuous f) (c : ℤ) (x : v.adicCompletion ℚ) :
    ∫ w, Kfun ψ f c x w ∂((μv v).prod (μv v)) = Hy v ψ f c x := by
  rw [integral_prod _ (integrable_Kfun hψc hf c x)]
  unfold Hy
  congr 1
  funext y
  simp only [Kfun_apply]
  rw [integral_const_mul]
  unfold Iz
  by_cases hy : y ∈ ball v c
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]

theorem whittakerDetector_eq_Dx (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1) {f : LocalGL3 v → ℂ} (hf : Continuous f) (c : ℤ) :
    whittakerDetector v ψ c f = Dx v ψ f c := by
  have hψc : Continuous ψ :=
    continuous_addChar_of_eq_one_on_ball v ψ 0 (fun x hx => hψ0 x (by simpa using hx))
  have hint := integrable_detectorIntegrand v hψc c hf
  rw [detectorIntegrand_eq] at hint
  unfold whittakerDetector
  rw [detectorIntegrand_eq, integral_prod _ hint]
  unfold Dx
  congr 1
  funext x
  dsimp only
  rw [integral_const_mul, integral_Kfun hψc hf c x]
  by_cases hx : x ∈ ball v c
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

end Link

section Corner

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] borelAdicCompletionC borelSpace_adicCompletionC

variable {v}

section Evals

variable {t : v.adicCompletion ℚ} (ht : Valued.v t = WithZero.exp 1)
include ht

theorem vt2 : Valued.v (t * t) = WithZero.exp 2 := by
  rw [map_mul, ht, ← WithZero.exp_add]; norm_num

omit ht in
theorem exp_le_exp' {m n : ℤ} (h : m ≤ n) : (WithZero.exp m : WithZero (Multiplicative ℤ)) ≤ WithZero.exp n :=
  WithZero.exp_le_exp.mpr h

omit ht in
theorem exp_lt_exp' {m n : ℤ} (h : m < n) : (WithZero.exp m : WithZero (Multiplicative ℤ)) < WithZero.exp n :=
  WithZero.exp_lt_exp.mpr h

omit ht in
theorem one_eq_exp_zero : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 := WithZero.exp_zero.symm

theorem evals_R0 {z : v.adicCompletion ℚ} (hz : Valued.v z ≤ 1) :
    e2 v 0 z = 1 ∧ e1 v 0 0 z = 1 ∧ e1 v 0 t z = WithZero.exp 1 ∧ e2 v t z = WithZero.exp 1 ∧
      e1 v t 0 z = 1 ∧ e1 v t t z = WithZero.exp 2 := by
  have h01 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 1 := by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)
  have h02 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)
  have h12 : (WithZero.exp 1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := exp_le_exp' (by norm_num)
  have hz1 : Valued.v z ≤ WithZero.exp 1 := hz.trans h01
  have hsm : Valued.v z < Valued.v (t * t) := by
    rw [vt2 ht]; exact lt_of_le_of_lt hz (by rw [one_eq_exp_zero]; exact exp_lt_exp' (by norm_num))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2_zero, max_eq_left hz]
  · rw [e1_zero_mid, max_eq_left hz]
  · rw [e1_of_valued_le_one v (by rw [map_zero]; exact zero_le'), ht, max_eq_left hz1, max_eq_right h01]
  · rw [e2, ht, max_eq_left hz1, max_eq_right h01]
  · rw [e1_zero_mid, max_eq_left hz]
  · rw [e1_small v hsm, ht, vt2 ht, max_eq_right h12, max_eq_right h02]

theorem evals_R1 {z : v.adicCompletion ℚ} (hz : Valued.v z = WithZero.exp 1) :
    e2 v 0 z = WithZero.exp 1 ∧ e1 v 0 0 z = WithZero.exp 1 ∧ e1 v 0 t z = WithZero.exp 1 ∧
      e2 v t z = WithZero.exp 1 ∧ e1 v t 0 z = WithZero.exp 1 ∧ e1 v t t z = WithZero.exp 2 := by
  have h01 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 1 := by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)
  have h02 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)
  have h12 : (WithZero.exp 1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := exp_le_exp' (by norm_num)
  have hsm : Valued.v z < Valued.v (t * t) := by rw [vt2 ht, hz]; exact exp_lt_exp' (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2_zero, hz, max_eq_right h01]
  · rw [e1_zero_mid, hz, max_eq_right h01]
  · rw [e1_of_valued_le_one v (by rw [map_zero]; exact zero_le'), ht, hz, max_self, max_eq_right h01]
  · rw [e2, ht, hz, max_self, max_eq_right h01]
  · rw [e1_zero_mid, hz, max_eq_right h01]
  · rw [e1_small v hsm, ht, vt2 ht, max_eq_right h12, max_eq_right h02]

theorem evals_R2 {z : v.adicCompletion ℚ} (hz : Valued.v z = WithZero.exp 2) :
    e2 v 0 z = WithZero.exp 2 ∧ e1 v 0 0 z = WithZero.exp 2 ∧ e1 v 0 t z = WithZero.exp 2 ∧
      e2 v t z = WithZero.exp 2 ∧ e1 v t 0 z = WithZero.exp 2 ∧
      e1 v t t z = max (WithZero.exp 1) (Valued.v (z - t * t)) := by
  have h01 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 1 := by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)
  have h02 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)
  have h12 : (WithZero.exp 1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := exp_le_exp' (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2_zero, hz, max_eq_right h02]
  · rw [e1_zero_mid, hz, max_eq_right h02]
  · rw [e1_of_valued_le_one v (by rw [map_zero]; exact zero_le'), ht, hz, max_eq_right h12, max_eq_right h02]
  · rw [e2, ht, hz, max_eq_right h12, max_eq_right h02]
  · rw [e1_zero_mid, hz, max_eq_right h02]
  · rw [e1, ht, ← max_assoc, max_eq_right h01]

theorem evals_tail {z : v.adicCompletion ℚ} (hz : WithZero.exp 3 ≤ Valued.v z) :
    e2 v 0 z = Valued.v z ∧ e1 v 0 0 z = Valued.v z ∧ e1 v 0 t z = Valued.v z ∧
      e2 v t z = Valued.v z ∧ e1 v t 0 z = Valued.v z ∧ e1 v t t z = Valued.v z := by
  have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v z :=
    le_trans (by rw [one_eq_exp_zero]; exact exp_le_exp' (by norm_num)) hz
  have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v z := lt_of_lt_of_le zero_lt_one h1
  have htz : Valued.v t ≤ Valued.v z := by rw [ht]; exact le_trans (exp_le_exp' (by norm_num)) hz
  have htt : Valued.v (t * t) < Valued.v z := by
    rw [vt2 ht]; exact lt_of_lt_of_le (exp_lt_exp' (by norm_num)) hz
  have h0z : Valued.v (0 : v.adicCompletion ℚ) ≤ Valued.v z := by rw [map_zero]; exact zero_le'
  have h00 : Valued.v ((0 : v.adicCompletion ℚ) * 0) < Valued.v z := by rwa [mul_zero, map_zero]
  have h0t : Valued.v ((0 : v.adicCompletion ℚ) * t) < Valued.v z := by rwa [zero_mul, map_zero]
  have ht0 : Valued.v (t * 0) < Valued.v z := by rwa [mul_zero, map_zero]
  exact ⟨e2_large v h1 h0z, e1_large v h1 h0z h00, e1_large v h1 htz h0t, e2_large v h1 htz,
    e1_large v h1 h0z ht0, e1_large v h1 htz htt⟩

end Evals

theorem corner_pointwise {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) f) (hf1 : f 1 = 1)
    {t : v.adicCompletion ℚ} (ht : Valued.v t = WithZero.exp 1) {c : ℤ} (hc : 1 ≤ c) (z : v.adicCompletion ℚ) :
    (ball v (2 * c)).indicator (Fw v f 0 0) z - (ball v (2 * c)).indicator (Fw v f 0 t) z
      - (ball v (2 * c)).indicator (Fw v f t 0) z + (ball v (2 * c)).indicator (Fw v f t t) z =
    (ball v 0).indicator (fun _ => (1 - PP v χ - QQ v χ + PP v χ ^ 2 * QQ v χ)) z +
      (ball v 1 \ ball v 0).indicator (fun _ => (PP v χ ^ 2 * QQ v χ - PP v χ * QQ v χ)) z +
      ((fun s => -(t * t) + s) ⁻¹' ball v 1).indicator (fun _ => (PP v χ * QQ v χ ^ 2 - PP v χ ^ 2 * QQ v χ ^ 2)) z := by
  have hF : ∀ a b z, Fw v f a b z = PP v χ ^ (e1 v a b z).log * QQ v χ ^ (e2 v a z).log := by
    intro a b z; rw [Fw_eq hχ hf hfK, hf1, one_mul]
  set P := PP v χ with hP
  set Q := QQ v χ with hQ
  have h2c : ball v 2 ⊆ ball v (2 * c) := ball_mono v (by omega)
  have hCsub : ∀ s, s ∈ (fun s => -(t * t) + s) ⁻¹' ball v 1 → Valued.v s = WithZero.exp 2 := by
    intro s hs
    have hs' : Valued.v (-(t * t) + s) ≤ WithZero.exp 1 := hs
    have hlt : Valued.v (-(t * t) + s) < Valued.v (t * t) := by
      rw [vt2 ht]; exact lt_of_le_of_lt hs' (by rw [WithZero.exp_lt_exp]; norm_num)
    have e : s = t * t + (-(t * t) + s) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ hlt, vt2 ht]
  by_cases hz0 : Valued.v z ≤ 1
  ·
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := evals_R0 ht hz0
    have hzB : z ∈ ball v (2 * c) := h2c (le_trans hz0 (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num))
    have hnC : z ∉ (fun s => -(t * t) + s) ⁻¹' ball v 1 := fun h => by
      have := hCsub z h
      rw [this, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz0; norm_num at hz0
    rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB,
      Set.indicator_of_mem (s := ball v 0) hz0, Set.indicator_of_notMem (s := ball v 1 \ ball v 0) (fun h => h.2 hz0),
      Set.indicator_of_notMem (s := (fun s => -(t * t) + s) ⁻¹' ball v 1) hnC,
      hF, hF, hF, hF, a1, a2, a3, a4, a5, a6]
    simp only [WithZero.log_one, WithZero.log_exp, zpow_zero, zpow_one, zpow_two]
    ring
  by_cases hz1 : Valued.v z ≤ WithZero.exp 1
  ·
    have hz : Valued.v z = WithZero.exp 1 :=
      le_antisymm hz1 (by have := exp_add_one_le_of_not_le (n := 0) hz0; simpa using this)
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := evals_R1 ht hz
    have hzB : z ∈ ball v (2 * c) := h2c (le_trans hz1 (by rw [WithZero.exp_le_exp]; norm_num))
    have hnC : z ∉ (fun s => -(t * t) + s) ⁻¹' ball v 1 := fun h => by
      have := hCsub z h
      rw [hz, WithZero.exp_inj] at this; norm_num at this
    rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB,
      Set.indicator_of_notMem (s := ball v 0) hz0, Set.indicator_of_mem (s := ball v 1 \ ball v 0) ⟨hz1, hz0⟩,
      Set.indicator_of_notMem (s := (fun s => -(t * t) + s) ⁻¹' ball v 1) hnC,
      hF, hF, hF, hF, a1, a2, a3, a4, a5, a6]
    simp only [WithZero.log_exp, zpow_one, zpow_two]
    ring
  by_cases hz2 : Valued.v z ≤ WithZero.exp 2
  ·
    have hz : Valued.v z = WithZero.exp 2 :=
      le_antisymm hz2 (by have := exp_add_one_le_of_not_le (n := 1) hz1; simpa using this)
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := evals_R2 ht hz
    have hzB : z ∈ ball v (2 * c) := h2c hz2
    rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB,
      Set.indicator_of_notMem (s := ball v 0) hz0, Set.indicator_of_notMem (s := ball v 1 \ ball v 0) (fun h => hz1 h.1),
      hF, hF, hF, hF, a1, a2, a3, a4, a5]
    by_cases hC : z ∈ (fun s => -(t * t) + s) ⁻¹' ball v 1
    · have hC' : Valued.v (z - t * t) ≤ WithZero.exp 1 := by
        have : Valued.v (-(t * t) + z) ≤ WithZero.exp 1 := hC
        rwa [neg_add_eq_sub] at this
      rw [Set.indicator_of_mem hC, a6, max_eq_left hC']
      simp only [WithZero.log_exp, zpow_one, zpow_two]
      ring
    · have hC' : Valued.v (z - t * t) = WithZero.exp 2 := by
        have hn : ¬ Valued.v (-(t * t) + z) ≤ WithZero.exp 1 := hC
        rw [neg_add_eq_sub] at hn
        refine le_antisymm ?_ (by have := exp_add_one_le_of_not_le (n := 1) hn; simpa using this)
        exact (Valuation.map_sub _ _ _).trans (max_le hz2 (vt2 ht).le)
      have h12 : (WithZero.exp 1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 2 := exp_le_exp' (by norm_num)
      rw [Set.indicator_of_notMem hC, a6, hC', max_eq_right h12]
      simp only [WithZero.log_exp, zpow_two]
      ring
  ·
    have hz3 : WithZero.exp 3 ≤ Valued.v z := by
      have := exp_add_one_le_of_not_le (n := 2) hz2; simpa using this
    have hnC : z ∉ (fun s => -(t * t) + s) ⁻¹' ball v 1 := fun h => by
      have := hCsub z h; rw [this] at hz2; exact hz2 le_rfl
    rw [Set.indicator_of_notMem (s := ball v 0) hz0, Set.indicator_of_notMem (s := ball v 1 \ ball v 0) (fun h => hz1 h.1),
      Set.indicator_of_notMem (s := (fun s => -(t * t) + s) ⁻¹' ball v 1) hnC]
    by_cases hzB : z ∈ ball v (2 * c)
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := evals_tail ht hz3
      rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB, Set.indicator_of_mem hzB,
        hF, hF, hF, hF, a1, a2, a3, a4, a5, a6]
      ring
    · rw [Set.indicator_of_notMem hzB, Set.indicator_of_notMem hzB, Set.indicator_of_notMem hzB,
        Set.indicator_of_notMem hzB]
      ring

theorem corner_integral {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) f) (hf1 : f 1 = 1)
    {t : v.adicCompletion ℚ} (ht : Valued.v t = WithZero.exp 1) {c : ℤ} (hc : 1 ≤ c) :
    Iz v f c 0 0 - Iz v f c 0 t - Iz v f c t 0 + Iz v f c t t =
      (V0 v : ℂ) * ((1 - PP v χ - QQ v χ + PP v χ ^ 2 * QQ v χ)
        + ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) - 1) * (PP v χ ^ 2 * QQ v χ - PP v χ * QQ v χ)
        + (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) * (PP v χ * QQ v χ ^ 2 - PP v χ ^ 2 * QQ v χ ^ 2)) := by
  have hfc : Continuous f := (isLocallyConstant_of_mem_principalSeries3 hf).continuous
  have hi := integrable_indicator_Fw (v := v) hfc c
  have hsum : Iz v f c 0 0 - Iz v f c 0 t - Iz v f c t 0 + Iz v f c t t =
      ∫ z, ((ball v (2 * c)).indicator (Fw v f 0 0) - (ball v (2 * c)).indicator (Fw v f 0 t)
        - (ball v (2 * c)).indicator (Fw v f t 0) + (ball v (2 * c)).indicator (Fw v f t t)) z ∂(μv v) := by
    unfold Iz
    rw [integral_add' (((hi 0 0).sub (hi 0 t)).sub (hi t 0)) (hi t t), integral_sub' ((hi 0 0).sub (hi 0 t)) (hi t 0),
      integral_sub' (hi 0 0) (hi 0 t)]
  rw [hsum]
  simp only [Pi.add_apply, Pi.sub_apply, corner_pointwise hχ hf hfK hf1 ht hc]
  have hmC : MeasurableSet ((fun s => -(t * t) + s) ⁻¹' ball v 1) := measurable_const_add _ (measurableSet_ball v 1)
  have hm10 : MeasurableSet (ball v 1 \ ball v 0) := (measurableSet_ball v 1).diff (measurableSet_ball v 0)
  have hi0 : Integrable ((ball v 0).indicator fun _ => (1 - PP v χ - QQ v χ + PP v χ ^ 2 * QQ v χ)) (μv v) :=
    integrable_indicator_of_continuous continuous_const (measurableSet_ball v 0) (subset_refl _)
  have hi1 : Integrable ((ball v 1 \ ball v 0).indicator fun _ => (PP v χ ^ 2 * QQ v χ - PP v χ * QQ v χ)) (μv v) :=
    integrable_indicator_of_continuous continuous_const hm10 Set.diff_subset
  have hi3 : Integrable (((fun s => -(t * t) + s) ⁻¹' ball v 1).indicator
      fun _ => (PP v χ * QQ v χ ^ 2 - PP v χ ^ 2 * QQ v χ ^ 2)) (μv v) := by
    refine integrable_indicator_of_continuous continuous_const hmC (k := 2) ?_
    intro s hs
    have hs' : Valued.v (-(t * t) + s) ≤ WithZero.exp 1 := hs
    have e : s = t * t + (-(t * t) + s) := by ring
    show Valued.v s ≤ WithZero.exp 2
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le (vt2 ht).le (hs'.trans (by rw [WithZero.exp_le_exp]; norm_num)))
  have hi01 : Integrable (fun z => (ball v 0).indicator (fun _ => (1 - PP v χ - QQ v χ + PP v χ ^ 2 * QQ v χ)) z +
      (ball v 1 \ ball v 0).indicator (fun _ => (PP v χ ^ 2 * QQ v χ - PP v χ * QQ v χ)) z) (μv v) := hi0.add hi1
  rw [integral_add hi01 hi3, integral_add hi0 hi1, integral_indicator_const _ (measurableSet_ball v 0),
    integral_indicator_const _ hm10, integral_indicator_const _ hmC, measureReal_diff (ball_mono v (by norm_num))
    (measurableSet_ball v 0) (measure_ball_lt_top v 1).ne, real_preimage_add, real_ball_one, V0]
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

end Corner

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] borelAdicCompletionC borelSpace_adicCompletionC

variable {v}

variable {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
  (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
  {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
  (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) f)

include hχ hf hfK

theorem isRadial_Iz {c : ℤ} (hc : 0 ≤ c) {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp c) :
    IsRadial v (Iz v f c x) where
  eq_zero y hy := Iz_of_valued_mid_le_one hχ hf hfK c x hy (by
    rw [map_mul]
    calc Valued.v x * Valued.v y ≤ WithZero.exp c * 1 := mul_le_mul' hx hy
      _ = WithZero.exp c := mul_one _
      _ ≤ WithZero.exp (2 * c) := WithZero.exp_le_exp.mpr (by omega))
  unit u y hu := Iz_unit_y hχ hf hfK c hu x y

theorem isRadial_Hy (ψ : AddChar (v.adicCompletion ℚ) ℂ) (c : ℤ) : IsRadial v (Hy v ψ f c) where
  eq_zero x hx := by
    unfold Hy
    congr 1
    funext y
    by_cases hy : y ∈ ball v c
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Iz_of_valued_le_one hχ hf hfK c hx y,
        Iz_of_valued_le_one hχ hf hfK c (x := 0) (by rw [map_zero]; exact zero_le') y]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  unit u x hu := by
    unfold Hy
    congr 1
    funext y
    by_cases hy : y ∈ ball v c
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Iz_unit_x hχ hf hfK c hu x y]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

variable (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψ x = 1)
  {a : v.adicCompletion ℚ} (ha1 : Valued.v a ≤ WithZero.exp 1) (ha : ψ a ≠ 1)
  {c : ℤ} (hc : 1 ≤ c) {t : v.adicCompletion ℚ} (ht : Valued.v t = WithZero.exp 1)

include hψ0 ha1 ha hc ht

theorem Hy_eq {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp c) :
    Hy v ψ f c x = (V0 v : ℂ) * (Iz v f c x 0 - Iz v f c x t) :=
  integral_ball_addChar_mul_radial ψ hψ0 ha1 ha (isRadial_Iz hχ hf hfK (by omega) hx) hc ht

theorem Dx_eq : Dx v ψ f c = (V0 v : ℂ) * (Hy v ψ f c 0 - Hy v ψ f c t) :=
  integral_ball_addChar_mul_radial ψ hψ0 ha1 ha (isRadial_Hy hχ hf hfK ψ c) hc ht

theorem whittakerDetector_eq (hf1 : f 1 = 1) :
    whittakerDetector v ψ c f =
      (V0 v : ℂ) ^ 3 * ((1 - PP v χ) * (1 - QQ v χ) * (1 - qv v * PP v χ * QQ v χ)) := by
  have hfc : Continuous f := (isLocallyConstant_of_mem_principalSeries3 hf).continuous
  rw [whittakerDetector_eq_Dx ψ hψ0 hfc c, Dx_eq hχ hf hfK ψ hψ0 ha1 ha hc ht,
    Hy_eq hχ hf hfK ψ hψ0 ha1 ha hc ht (x := 0) (by rw [map_zero]; exact zero_le'),
    Hy_eq hχ hf hfK ψ hψ0 ha1 ha hc ht (x := t) (by rw [ht]; exact WithZero.exp_le_exp.mpr hc)]
  have h := corner_integral hχ hf hfK hf1 ht hc
  unfold qv
  linear_combination ((V0 v : ℂ)) ^ 2 * h

omit hχ hf hfK hψ0 ha1 ha hc ht

theorem ne_one_of_norm_eq_inv {w : ℂ} (hw : ‖w‖ = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ))⁻¹) : w ≠ 1 := by
  intro h
  rw [h, norm_one] at hw
  have hq : (1 : ℝ) < (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) := by exact_mod_cast one_lt_natCard_quot v
  have : (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) = 1 := by
    have hpos : (0 : ℝ) < (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) := by linarith
    field_simp at hw
    linarith
  linarith

theorem norm_qv : ‖qv v‖ = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) := by
  unfold qv; exact Complex.norm_natCast _

variable (hχu : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
include hχu

theorem norm_PP : ‖PP v χ‖ = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ))⁻¹ := by
  unfold PP alpha
  rw [norm_mul, norm_mul, norm_inv, norm_inv, hχu, hχu, norm_qv]
  simp

theorem norm_QQ : ‖QQ v χ‖ = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ))⁻¹ := by
  unfold QQ alpha
  rw [norm_mul, norm_mul, norm_inv, norm_inv, hχu, hχu, norm_qv]
  simp

theorem norm_qPQ : ‖qv v * PP v χ * QQ v χ‖ = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ))⁻¹ := by
  rw [norm_mul, norm_mul, norm_PP hχu, norm_QQ hχu, norm_qv]
  have hq : (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ≠ 0 := by
    have := one_lt_natCard_quot v
    exact_mod_cast (show Nat.card (𝓞 ℚ ⧸ v.asIdeal) ≠ 0 by omega)
  field_simp

include hχ hf hfK hψ0 ha1 ha hc ht in

theorem whittakerDetector_ne_zero (hf1 : f 1 = 1) : whittakerDetector v ψ c f ≠ 0 := by
  rw [whittakerDetector_eq hχ hf hfK ψ hψ0 ha1 ha hc ht hf1]
  refine mul_ne_zero (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (V0_pos v).ne')) ?_
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact sub_ne_zero.mpr (ne_one_of_norm_eq_inv (norm_PP hχu)).symm
  · exact sub_ne_zero.mpr (ne_one_of_norm_eq_inv (norm_QQ hχu)).symm
  · exact sub_ne_zero.mpr (ne_one_of_norm_eq_inv (norm_qPQ hχu)).symm

end Assembly

end CSNV

open CSNV in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1)
    (hχu : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f : ↥(principalSeries3 v χ)) (hf1 : (f : LocalGL3 v → ℂ) 1 = 1)
    (hfK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (f : LocalGL3 v → ℂ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerFunctional3 ψv Λ) (hΛne : Λ ≠ 0) :
    Λ f ≠ 0 := by
  obtain ⟨a, ha1, ha⟩ := hψ1
  have hψne : ψv ≠ 1 := by
    intro h
    apply ha
    rw [h]
    rfl
  obtain ⟨t, -, ht⟩ := exists_valued_eq_exp v 1
  refine whittaker_apply_ne_zero_of_detector_ne_zero v χ ψv (m := 0) (fun x hx => hψ0 x (by simpa using hx)) hψne
    f 1 (fun c hc => ?_) Λ hΛ hΛne
  exact whittakerDetector_ne_zero hχ f.2 hfK ψv hψ0 ha1 ha hc ht hχu hf1

end PartE

end

end S_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one (solution)
