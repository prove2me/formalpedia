-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6bad4183-877a-5924-947f-e5254171b9d3

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

section
open MeasureTheory Set

namespace Ws23Z30

namespace AbsInvDensity

noncomputable def nnDensity (y : ℝ) : NNReal := Real.toNNReal |y|⁻¹

theorem measurable_nnDensity : Measurable nnDensity :=
  (measurable_abs.inv).real_toNNReal

theorem coe_nnDensity (y : ℝ) : (nnDensity y : ℝ) = |y|⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg y))

theorem pos_of_map_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) : 0 < κ := by
  by_contra hle
  have h0 : ENNReal.ofReal κ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
  have hmap : Measure.map T μ = 0 := by rw [hκ, h0, zero_smul]
  apply hμ
  rw [← Measure.measure_univ_eq_zero, ← Set.preimage_univ (f := T), ← Measure.map_apply hT MeasurableSet.univ, hmap]
  rfl

theorem map_eq_smul_withDensity {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => (nnDensity y : ENNReal) := hκ

theorem map_absolutelyContinuous {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ ≪ (volume : Measure ℝ) := by
  rw [hκ]
  exact (withDensity_absolutelyContinuous _ _).smul_left (ENNReal.ofReal κ)

theorem nnDensity_smul_eq (f : ℝ → ℂ) (y : ℝ) : nnDensity y • f y = f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  change ((nnDensity y : ℝ)) • f y = f y * ((|y| : ℝ) : ℂ)⁻¹
  rw [Complex.real_smul, coe_nnDensity, Complex.ofReal_inv, mul_comm]

theorem integral_comp_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T)
    (κ : ℝ) (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    0 < κ ∧ ∫ x, f (T x) ∂μ = (κ : ℂ) * ∫ y : ℝ, f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  have hpos : 0 < κ := pos_of_map_eq μ T hT κ hκ hμ
  refine ⟨hpos, ?_⟩
  have hf' : AEStronglyMeasurable f (Measure.map T μ) := hf.mono_ac (map_absolutelyContinuous μ T κ hκ)
  rw [← integral_map hT.aemeasurable hf', map_eq_smul_withDensity μ T κ hκ, integral_smul_measure,
    integral_withDensity_eq_integral_smul measurable_nnDensity, ENNReal.toReal_ofReal hpos.le]
  refine Complex.real_smul.trans ?_
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => nnDensity_smul_eq f y)

end AbsInvDensity

theorem norm_component_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x Rat.infinitePlace‖ = |StandardKernel.realCoord x| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (Rat.isReal_infinitePlace)).norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  rw [← h, Real.norm_eq_abs]
  rfl

theorem ideleChar_section_eq_quasiChar_realCoord
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((σ (E z) : ℂˣ) : ℂ) = ArchR.quasiChar t (e : ZMod 2) (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) := by
  have hvr : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace
  let zv : ((Rat.infinitePlace).Completion)ˣ :=
    Units.map (Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).toMonoidHom z
  have hzv : ((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion) =
      (z : InfiniteAdeleRing ℚ) Rat.infinitePlace := rfl
  obtain ⟨h1, h2⟩ := hE z
  have h1' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = (z : InfiniteAdeleRing ℚ) := by
    have h := congrArg Units.val h1
    simp [M4aHerbrand.infPart] at h
    exact h
  have h2' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have h := congrArg Units.val h2
    simp [RatIdele.finPart] at h
    exact h
  have hEz : E z = NumberField.TateGlobal.archUnitHom Rat.infinitePlace zv := by
    apply Units.ext
    refine Prod.ext ?_ ?_
    · rw [h1']
      funext w
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      simp [NumberField.TateGlobal.archUnitHom, NumberField.AdelicVolume.archCentralUnit, hzv]
    · exact h2'
  have hloc := hσ Rat.infinitePlace hvr zv
  have hσE : ((σ (E z) : ℂˣ) : ℂ) =
      ((NumberField.TateGlobal.archLocalChar σ Rat.infinitePlace zv : ℂˣ) : ℂ) := by
    rw [hEz]; rfl
  rw [hσE, hloc]
  set r : ℝ := StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) with hr
  have hnorm : ‖((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion)‖ = |r| := by
    rw [hzv, hr]; exact norm_component_eq_abs_realCoord _
  have hemb : InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
      ((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion) = (r : ℂ) := by
    rw [hzv, hr, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hvr]
    rfl
  have hmult : ((Rat.infinitePlace).mult : ℂ) = 1 := by
    have h : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, hvr⟩
    rw [h]; norm_num
  have hr0 : r ≠ 0 := (z.isUnit.map StandardKernel.realCoord).ne_zero
  rw [hnorm, hemb, hmult, one_mul]
  unfold ArchR.quasiChar
  congr 1
  have hcast : ((e : ZMod 2) = 0) ↔ Even e := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    norm_cast
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have habs : |r| = -r := abs_of_neg hneg
    have hsign : SignType.sign r = -1 := sign_neg hneg
    rw [habs, hsign]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
    by_cases he : Even e
    · rw [he.neg_one_zpow, if_pos (hcast.mpr he)]
    · rw [(Int.not_even_iff_odd.mp he).neg_one_zpow, if_neg (fun h => he (hcast.mp h))]
      simp
  · have habs : |r| = r := abs_of_pos hpos
    have hsign : SignType.sign r = 1 := sign_pos hpos
    rw [habs, hsign, div_self (by exact_mod_cast hr0), one_zpow]
    split_ifs <;> simp

theorem norm_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x‖ = |StandardKernel.realCoord x| := by
  rw [InfiniteAdeleRing.norm_def, Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  have hm : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  rw [hd, hm, pow_one]
  exact norm_component_eq_abs_realCoord x

theorem measurable_realCoord_units [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] :
    Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  have hc : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (continuous_apply Rat.infinitePlace)
  exact (hc.comp Units.continuous_val).measurable

end Ws23Z30

end

open scoped Classical in
open LanglandsTunnell LanglandsTunnell.CubicInduction in
theorem solution
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Φ : ℝ → ℂ)
    (hW : ∀ z : (InfiniteAdeleRing ℚ)ˣ,
      W (iotaGL (diagUnitGL2 z) * 1) = Φ (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)))
    (hΦ : MeasureTheory.AEStronglyMeasurable Φ MeasureTheory.volume) (s : ℂ) :
    0 < κ ∧
      archZeta30 ν_mul W (σ.comp E) s 1 =
        (κ : ℂ) * ∫ y : ℝ, Φ y * ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ := by
  have hT : Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
    Ws23Z30.measurable_realCoord_units
  have hν : ν_mul ≠ 0 := NeZero.ne ν_mul

  set f : ℝ → ℂ := fun y => Φ y * ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) with hf
  have hfm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume := by
    have hsign : Measurable fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ) := by
      have : (fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ)) =
          fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
        funext y; rw [sign_apply]; split_ifs <;> simp
      rw [this]
      exact Measurable.ite measurableSet_Ioi measurable_const
        (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    have hq : Measurable fun y : ℝ => ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) := by
      unfold ArchR.quasiChar
      refine ((((Complex.measurable_ofReal.comp measurable_abs).pow_const t).mul ?_).mul
        ((Complex.measurable_ofReal.comp measurable_abs).pow_const (s - 1)))
      split_ifs
      · exact measurable_const
      · exact hsign
    refine (hΦ.mul hq.aestronglyMeasurable).congr (MeasureTheory.ae_of_all _ fun y => ?_)
    simp only [hf, Pi.mul_apply]
    ring
  have h1 : (fun z : (InfiniteAdeleRing ℚ)ˣ => W (iotaGL (diagUnitGL2 z) * 1) * (((σ.comp E) z : ℂˣ) : ℂ) *
      ((‖(z : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) =
      fun z : (InfiniteAdeleRing ℚ)ˣ => f (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) := by
    funext z
    simp only [hf, hW z, MonoidHom.comp_apply, Ws23Z30.ideleChar_section_eq_quasiChar_realCoord σ t e hσ E hE z,
      Ws23Z30.norm_eq_abs_realCoord]
  obtain ⟨hpos, hint⟩ := Ws23Z30.AbsInvDensity.integral_comp_eq ν_mul _ hT κ hκ hν f hfm
  refine ⟨hpos, ?_⟩
  unfold archZeta30
  rw [h1, hint]

#print axioms solution

end S_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt (solution)
