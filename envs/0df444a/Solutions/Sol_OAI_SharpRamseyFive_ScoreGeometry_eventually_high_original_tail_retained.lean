-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:37:58.253647+00:00
-- url     : https://prove2.me/submissions/65ceebb8-794b-44cb-910f-cf042c730031

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_actual_high_radial_moment

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

lemma finite_bounds {η σ D R : ℝ} (hη : 0 < η) (_hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) :
    0 < D ∧ 0 < R ∧ 1 ≤ σ ^ beta η ∧
    σ ^ (9 * beta η) ≤ L η σ D ∧ L η σ D ≤ σ ∧
    σ ^ (10 * beta η) ≤ P η σ D R ∧
    P η σ D R ≤ 4 * σ ^ (1 - η/2 + 9 * beta η) := by
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hb : 0 < beta η := beta_pos hη
  have hx : 1 ≤ σ ^ beta η := Real.one_le_rpow hσ hb.le
  have hd : 0 < D := (Real.rpow_pos_of_pos hs _).trans_le h.dlo
  have hr : 0 < R := (Real.rpow_pos_of_pos hs _).trans_le h.rlo
  have hlo : σ ^ (9 * beta η) ≤ L η σ D := by
    dsimp [L]
    calc
      _ = σ ^ beta η * σ ^ (8 * beta η) := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.dlo (Real.rpow_nonneg hs.le _)
  have hhi : L η σ D ≤ σ := by
    dsimp [L]
    calc
      _ ≤ σ ^ (1-η/2) * σ ^ (8*beta η) := mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)
      _ = σ ^ (1-η/2+8*beta η) := (Real.rpow_add hs _ _).symm
      _ ≤ σ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hσ (by dsimp [beta]; linarith)
      _ = σ := Real.rpow_one _
  refine ⟨hd,hr,hx,hlo,hhi,?_,?_⟩
  · calc
      _ = σ ^ (9*beta η) * σ ^ beta η := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ L η σ D * R := mul_le_mul hlo h.rlo (Real.rpow_nonneg hs.le _) (by dsimp [L]; positivity)
  · have hR : R ≤ 4 * σ ^ beta η := h.rhi.trans (by linarith)
    calc
      _ ≤ (σ ^ (1-η/2) * σ ^ (8*beta η)) * (4*σ ^ beta η) := by
        dsimp [P,L]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)) hR hr.le (by positivity)
      _ = 4 * σ ^ (1-η/2+9*beta η) := by
        rw [show σ ^ (1-η/2) * σ ^ (8*beta η) * (4*σ ^ beta η) =
          4 * ((σ ^ (1-η/2) * σ ^ (8*beta η)) * σ ^ beta η) by ring,
          ← Real.rpow_add hs, ← Real.rpow_add hs]
        congr 2
        ring

lemma ratio_bounds {η σ D R b τ : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) (Cb : ℝ) (_hCb : 0 ≤ Cb)
    (hb : b ≤ Cb * D * σ ^ (6*beta η)) (hτ : τ ≤ σ ^ (-200*beta η)) :
    P η σ D R / σ ≤ 4*σ ^ (-(η/2-9*beta η)) ∧
    Real.log σ / P η σ D R ≤ Real.log σ / σ ^ (10*beta η) ∧
    R * Real.log (L η σ D) / P η σ D R ≤ Real.log σ / σ ^ (9*beta η) ∧
    (b + P η σ D R * τ) / L η σ D ≤ Cb*σ ^ (-2*beta η) + 4*σ ^ (-199*beta η) ∧
    L η σ D / P η σ D R ≤ σ ^ (-beta η) := by
  obtain ⟨hD,hR,hx,hL,hLhi,hP,hPhi⟩ := finite_bounds hη hη' hσ h
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hLp : 0 < L η σ D := (Real.rpow_pos_of_pos hs _).trans_le hL
  have hPp : 0 < P η σ D R := (Real.rpow_pos_of_pos hs _).trans_le hP
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      _ ≤ (4*σ ^ (1-η/2+9*beta η))/σ := div_le_div_of_nonneg_right hPhi hs.le
      _ = _ := by
        rw [mul_div_assoc]
        have he : σ ^ (1-η/2+9*beta η) / σ = σ ^ (1-η/2+9*beta η-1) := by
          simpa only [Real.rpow_one] using (Real.rpow_sub hs (1-η/2+9*beta η) 1).symm
        rw [he]
        congr 2
        ring
  · exact div_le_div_of_nonneg_left (Real.log_nonneg hσ) (Real.rpow_pos_of_pos hs _) hP
  · have he : R * Real.log (L η σ D) / P η σ D R = Real.log (L η σ D) / L η σ D := by
      dsimp [P]; field_simp
    rw [he]
    exact (div_le_div_of_nonneg_right (Real.log_le_log hLp hLhi) hLp.le).trans
      (div_le_div_of_nonneg_left (Real.log_nonneg hσ) (Real.rpow_pos_of_pos hs _) hL)
  · have hRhi : R ≤ 4*σ ^ beta η := h.rhi.trans (by linarith)
    have hf : (b + P η σ D R*τ)/L η σ D = b/L η σ D + R*τ := by
      dsimp [P]; field_simp
    rw [hf]
    have hb' : b/L η σ D ≤ Cb*σ ^ (-2*beta η) := by
      apply (div_le_iff₀ hLp).mpr
      calc
        b ≤ Cb*D*σ ^ (6*beta η) := hb
        _ = _ := by
          dsimp [L]
          rw [show Cb*σ ^ (-2*beta η)*(D*σ ^ (8*beta η)) =
            Cb*D*(σ ^ (-2*beta η)*σ ^ (8*beta η)) by ring, ← Real.rpow_add hs]
          congr 2
          ring
    have ht' : R*τ ≤ 4*σ ^ (-199*beta η) := by
      calc
        _ ≤ R*σ ^ (-200*beta η) := mul_le_mul_of_nonneg_left hτ hR.le
        _ ≤ (4*σ ^ beta η)*σ ^ (-200*beta η) :=
          mul_le_mul_of_nonneg_right hRhi (Real.rpow_nonneg hs.le _)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hs]; congr 2; ring
    exact add_le_add hb' ht'
  · apply (div_le_iff₀ hPp).mpr
    change L η σ D ≤ σ ^ (-beta η) * (L η σ D * R)
    have he : σ ^ (-beta η)*σ ^ beta η = 1 := by rw [← Real.rpow_add hs]; simp
    have hh := mul_le_mul_of_nonneg_left h.rlo (Real.rpow_nonneg hs.le (-beta η))
    rw [he] at hh
    nlinarith

theorem eventually_hierarchy {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb c A : ℝ) (hCb : 0 ≤ Cb) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ D R b τ : ℝ, Range η σ D R →
      b ≤ Cb*D*σ ^ (6*beta η) → τ ≤ σ ^ (-200*beta η) →
      A ≤ L η σ D ∧ P η σ D R ≤ c*σ ∧
      Real.log σ ≤ c*P η σ D R ∧
      R*Real.log (L η σ D) ≤ c*P η σ D R ∧
      b+P η σ D R*τ ≤ c*L η σ D ∧ L η σ D ≤ c*P η σ D R := by
  have hb : 0 < beta η := beta_pos hη
  have he : 0 < η/2-9*beta η := by dsimp [beta]; linarith
  have h1 : Tendsto (fun σ : ℝ => 4*σ ^ (-(η/2-9*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop he).const_mul 4
  have h2 := (isLittleO_log_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) hb)).tendsto_div_nhds_zero
  have h3 := (isLittleO_log_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<9) hb)).tendsto_div_nhds_zero
  have h4 : Tendsto (fun σ : ℝ => Cb*σ ^ (-2*beta η)+4*σ ^ (-199*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul, mul_zero, zero_add] using
      ((tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<2) hb)).const_mul Cb).add
      ((tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<199) hb)).const_mul 4)
  have h5 := tendsto_rpow_neg_atTop hb
  have h6 := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<9) hb)).eventually (eventually_ge_atTop A)
  filter_upwards [eventually_ge_atTop (1:ℝ), h1.eventually_lt_const hc,
    h2.eventually_lt_const hc, h3.eventually_lt_const hc, h4.eventually_lt_const hc,
    h5.eventually_lt_const hc, h6] with σ hσ h1' h2' h3' h4' h5' h6'
  intro D R b τ h hb' hτ
  obtain ⟨hD,hR,_,hL,_,hP,_⟩ := finite_bounds hη hη' hσ h
  obtain ⟨hr1,hr2,hr3,hr4,hr5⟩ := ratio_bounds hη hη' hσ h Cb hCb hb' hτ
  have hLp : 0 < L η σ D := by dsimp [L]; positivity
  have hPp : 0 < P η σ D R := mul_pos hLp hR
  exact ⟨h6'.trans hL, (div_le_iff₀ (zero_lt_one.trans_le hσ)).mp (hr1.trans h1'.le),
    (div_le_iff₀ hPp).mp (hr2.trans h2'.le), (div_le_iff₀ hPp).mp (hr3.trans h3'.le),
    (div_le_iff₀ hLp).mp (hr4.trans h4'.le), (div_le_iff₀ hPp).mp (hr5.trans h5'.le)⟩

theorem eventually_power_absorption {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (C k c : ℝ) (hC : 0 < C) (_hk : 0 ≤ k) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ D R : ℝ, Range η σ D R →
      C*σ ^ k ≤ Real.exp (c*P η σ D R) := by
  have hb : 0 < 10*beta η := mul_pos (by norm_num) (beta_pos hη)
  have hlog : Tendsto (fun σ : ℝ => (Real.log C+k*Real.log σ)/σ ^ (10*beta η)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun σ : ℝ => Real.log C/σ ^ (10*beta η)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hb)
    have hvar := ((isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero).const_mul k
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hconst.add hvar
  filter_upwards [eventually_ge_atTop (1:ℝ), hlog.eventually_lt_const hc] with σ hσ hh
  intro D R h
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hPs := (finite_bounds hη hη' hσ h).2.2.2.2.2.1
  have hcost : Real.log C+k*Real.log σ ≤ c*P η σ D R :=
    ((div_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp hh.le).trans
      (mul_le_mul_of_nonneg_left hPs hc.le)
  apply (Real.log_le_iff_le_exp (mul_pos hC (Real.rpow_pos_of_pos hs _))).mp
  rwa [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hs k).ne', Real.log_rpow hs]

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace RadialLine

lemma through_eq_iff [FiniteDimensional K V] {x y : ℙ K V} (hxy : x ≠ y)
    (l : RadialLine x) : through x y hxy = l ↔ y.submodule ≤ l.val := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (sup_le l.property.2 h)
      ((finrank_sup_points hxy).trans l.property.1.symm)

lemma through_le_iff {x y : ℙ K V} (hxy : x ≠ y) (W : Submodule K V) :
    (through x y hxy).val ≤ W ↔ x.submodule ≤ W ∧ y.submodule ≤ W :=
  sup_le_iff

section RadialMass

open scoped Classical

variable [FiniteDimensional K V] {x : ℙ K V} [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma trainingOnLine_eq_fiber (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) :
    trainingOnLine X l = X.filter (fun y => through x y.val y.property = l) := by
  classical
  ext y
  simp only [trainingOnLine, Finset.mem_filter, through_eq_iff]

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma abs_centeredFactor_le_one (s : Finset ι) (b : ℝ) (hb : b ∈ Set.Icc 0 1)
    (ω : ι → ℕ) : |centeredFactor s b ω| ≤ 1 := by
  unfold centeredFactor emptyIndicator
  by_cases h : ω ∈ emptyEvent s <;> simp [h, abs_le] <;> constructor <;> linarith [hb.1, hb.2]

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
lemma measurePreserving_partition (rate : ι → ℝ≥0) (label : ι → κ) :
    MeasurePreserving (partitionEquiv label) (batchMeasure rate)
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
  have hc : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))
      (Measure.pi (fun p : (c : κ) × {i : ι // label i = c} => poissonMeasure (rate p.2)))
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
    refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, batchMeasure] using
      Measure.infinitePi_map_piCurry (fun (c : κ) (i : {i : ι // label i = c}) =>
        poissonMeasure (rate i))
  exact hc.comp ((measurePreserving_piCongrLeft (fun i => poissonMeasure (rate i))
    (Equiv.sigmaFiberEquiv label)).symm)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

lemma lineTrunc_range (J : ℕ) (ω : Fin R → ℕ) :
    lineTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by unfold lineTrunc; split_ifs <;> norm_num

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ComponentLabelWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)

omit [DecidableEq D] in
lemma allTrunc_range (J : ℕ) (ω : Fin R × D → ℕ) :
    allTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => (lineTrunc_range R J _).1)
  · exact Finset.prod_le_one (fun _ _ => (lineTrunc_range R J _).1)
      (fun _ _ => (lineTrunc_range R J _).2)

end SharpRamseyFive.HighMoment
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighBudgetPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open scoped BigOperators

lemma highMomentBudget_normalized (Q a B b L : ℝ) (p R N₂ : ℕ)
    (hB : 0<B) (hb : 0<b) :
    highMomentBudget Q (a*B^2) (a*B) B b L p R N₂ =
      B*(2+1/B+(p:ℝ)^2*(Q/(B*b^8))+
        (p:ℝ)^4*((N₂:ℝ)*b/B)*(200*p+2*((R:ℝ)*L))^2+
        (p:ℝ)^4*(((R:ℝ)*L)^200*a+(Q/B^2)*(2*((R:ℝ)*L))^200)+
        2*(p:ℝ)^200*a+Q/B^2) := by
  unfold highMomentBudget highCertificateMajorant
  field_simp
  ring

lemma highMomentBudget_le_poly (Q a B b L : ℝ) (p R N₂ : ℕ)
    (hB : 1≤B) (hb : 0<b) (_ha : 0≤a) (_hL : 0≤L)
    (hroot : Q/(B*b^8)≤40) (hanchor : (N₂:ℝ)*b/B≤20) (hpair : Q/B^2≤400) :
    highMomentBudget Q (a*B^2) (a*B) B b L p R N₂ ≤
      B*highBudgetPoly a p ((R:ℝ)*L) := by
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  rw [highMomentBudget_normalized Q a B b L p R N₂ hB0 hb]
  unfold highBudgetPoly
  apply mul_le_mul_of_nonneg_left _ hB0.le
  have hBi : 1/B≤1 := (div_le_one hB0).mpr hB
  calc
    _ ≤ 2+1+(p:ℝ)^2*40+(p:ℝ)^4*20*(200*p+2*((R:ℝ)*L))^2+
        (p:ℝ)^4*(((R:ℝ)*L)^200*a+400*(2*((R:ℝ)*L))^200)+2*(p:ℝ)^200*a+400 := by
      gcongr
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DyadCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma dyad_count_le {m : ℕ} {σ : ℝ} (hσ : 1≤σ)
    (hm : (m:ℝ)≤Real.exp (3*σ)) : (Nat.clog 2 m:ℝ)+1≤8*σ := by
  by_cases hm1 : m≤1
  · rw [Nat.clog_of_right_le_one hm1]
    simp only [Nat.cast_zero,zero_add]
    linarith
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hml : 0≤Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmlhi : Real.log (m:ℝ)≤3*σ := (Real.log_le_iff_le_exp hm0).mpr hm
  have hlog : Real.logb 2 (m:ℝ)≤6*σ := by
    rw [Real.logb]
    apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
    nlinarith
  have hc := Nat.ceil_lt_add_one (show 0≤Real.logb 2 (m:ℝ) by
    rw [Real.logb]; exact div_nonneg hml (by linarith))
  have he := Real.natCeil_logb_natCast 2 m
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hc
  linarith

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighPolyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

lemma highPolyConstant_pos {k c : ℝ} (hk : 0≤k) (hc : 0 ≤ c) : 0<highPolyConstant k c := by
  unfold highPolyConstant
  positivity

lemma highBudgetPoly_bound {σ E p P a k c : ℝ}
    (hσ : 1≤σ) (hE : 1≤E) (hp : 0≤p) (hphi : p≤k*σ)
    (hP : 0≤P) (hPhi : P≤σ) (ha : 0≤a) (hahi : a ≤ c*σ*E)
    (hk : 0≤k) (hc : 0 ≤ c) :
    highBudgetPoly a p P≤highPolyConstant k c*σ^(205:ℕ)*E := by
  have hσ0 : 0≤σ := by linarith
  have hE0 : 0≤E := by linarith
  have hpow (j : ℕ) (hj : j≤205) : σ^j≤σ^(205:ℕ) := pow_le_pow_right₀ hσ hj
  have hpowE (j : ℕ) (hj : j≤205) : σ^j≤σ^(205:ℕ)*E :=
    (hpow j hj).trans (le_mul_of_one_le_right (pow_nonneg hσ0 _) hE)
  have h1 : 1≤σ^(205:ℕ)*E := by simpa using hpowE 0 (by omega)
  have hr : 40*p^2≤(40*k^2)*σ^(205:ℕ)*E := by
    calc
      _ ≤ 40*(k*σ)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hphi 2) (by norm_num)
      _ = (40*k^2)*σ^2 := by ring
      _ ≤ (40*k^2)*(σ^(205:ℕ)*E) := mul_le_mul_of_nonneg_left (hpowE 2 (by omega)) (by positivity)
      _ = _ := by ring
  have hbase : 200*p+2*P≤(200*k+2)*σ := by nlinarith
  have ht : 20*p^4*(200*p+2*P)^2≤(20*k^4*(200*k+2)^2)*σ^(205:ℕ)*E := by
    calc
      _ ≤ 20*(k*σ)^4*((200*k+2)*σ)^2 := by gcongr
      _ = (20*k^4*(200*k+2)^2)*σ^6 := by ring
      _ ≤ (20*k^4*(200*k+2)^2)*(σ^(205:ℕ)*E) :=
        mul_le_mul_of_nonneg_left (hpowE 6 (by omega)) (by positivity)
      _ = _ := by ring
  have hm : p^4*(P^200*a+400*(2*P)^200)≤
      (k^4*(c+400*2^(200:ℕ)))*σ^(205:ℕ)*E := by
    calc
      _ ≤ (k*σ)^4*(σ^200*(c*σ*E)+400*(2*σ)^200) := by
        apply mul_le_mul (pow_le_pow_left₀ hp hphi 4)
        · exact add_le_add
            (mul_le_mul (pow_le_pow_left₀ hP hPhi 200) hahi ha (pow_nonneg hσ0 _))
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg (by norm_num) hP)
                (mul_le_mul_of_nonneg_left hPhi (by norm_num)) 200) (by norm_num))
        · exact add_nonneg (mul_nonneg (pow_nonneg hP _) ha)
            (mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) hP) _))
        · exact pow_nonneg (mul_nonneg hk hσ0) _
      _ = k^4*c*σ^(205:ℕ)*E+(400*k^4*2^(200:ℕ))*σ^(204:ℕ) := by ring
      _ ≤ k^4*c*σ^(205:ℕ)*E+(400*k^4*2^(200:ℕ))*(σ^(205:ℕ)*E) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hpowE 204 (by omega))
          (show 0≤400*k^4*2^(200:ℕ) from mul_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg hk _)) (pow_nonneg (by norm_num) _)))
      _ = _ := by ring
  have hs : 2*p^200*a≤(2*k^200*c)*σ^(205:ℕ)*E := by
    calc
      _ ≤ 2*(k*σ)^200*(c*σ*E) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hphi 200) (by norm_num)) hahi ha
        (mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg hk hσ0) _))
      _ = (2*k^200*c)*σ^(201:ℕ)*E := by ring
      _ ≤ (2*k^200*c)*σ^(205:ℕ)*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpow 201 (by omega))
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hk _)) hc)) hE0
  unfold highBudgetPoly
  calc
    _ ≤ 3*(σ^(205:ℕ)*E)+(40*k^2)*σ^(205:ℕ)*E+
        (20*k^4*(200*k+2)^2)*σ^(205:ℕ)*E+
        (k^4*(c+400*2^(200:ℕ)))*σ^(205:ℕ)*E+
        (2*k^200*c)*σ^(205:ℕ)*E+400*(σ^(205:ℕ)*E) := by
      have h3 : (3:ℝ)≤3*(σ^(205:ℕ)*E) := by linarith
      have h400 : (400:ℝ)≤400*(σ^(205:ℕ)*E) := by linarith
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h3 hr) ht) hm) hs) h400
    _ = _ := by unfold highPolyConstant; ring

lemma dyadFactor_exp_bound {σ P : ℝ} {m : ℕ} (hσ : 1≤σ)
    (hm : (m:ℝ)≤Real.exp (3*σ)) :
    dyadFactor m (P/100)≤(8*2^(200:ℕ))*σ*Real.exp (P/50) := by
  unfold dyadFactor
  have hdy := dyad_count_le hσ hm
  rw [show (2:ℝ)*(P/100)=P/50 by ring]
  calc
    _ ≤ 2^(200:ℕ)*(8*σ)*Real.exp (P/50) := by gcongr
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EventuallyHighPolyCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_high_poly_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (k c : ℝ) (hk : 0≤k) (hc : 0 ≤ c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R p a : ℝ,Range η σ D R →
      0≤p → p≤k*σ → 0≤a → a ≤ c*σ*Real.exp (P η σ D R/50) →
      Real.exp (P η σ D R/50)+2*(p+1)*highBudgetPoly a p (P η σ D R)≤
        Real.exp (P η σ D R/5) := by
  let C := highPolyConstant k c
  have hC : 0<C := highPolyConstant_pos hk hc
  have hK : 0<1+2*(k+1)*C := by positivity
  have hab := eventually_power_absorption hη hη' (1+2*(k+1)*C) 206 (1/10)
    hK (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R p a hr hp hphi ha hahi
  have hpar := finite_bounds hη hη' hσ hr
  have hP : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hpar.2.2.2.2.2.1
  have hPhi : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hpol := highBudgetPoly_bound hσ (Real.one_le_exp_iff.mpr (by positivity : 0≤P η σ D R/50))
    hp hphi hP hPhi ha hahi hk hc
  have hcoef : 1+2*(p+1)*C*σ^(205:ℕ)≤(1+2*(k+1)*C)*σ^(206:ℕ) := by
    have hh : p+1≤(k+1)*σ := by nlinarith
    have h1 : 1≤σ^(206:ℕ) := one_le_pow₀ hσ
    calc
      _ ≤ σ^(206:ℕ)+2*((k+1)*σ)*C*σ^(205:ℕ) := by gcongr
      _ = _ := by rw [show σ^(206:ℕ)=σ^205*σ from pow_succ σ 205]; ring
  have hh : (1+2*(k+1)*C)*σ^(206:ℕ)≤Real.exp (P η σ D R/10) := by
    have ht := hab D R hr
    rw [show σ^(206:ℝ)=σ^(206:ℕ) from Real.rpow_natCast σ 206] at ht
    simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using ht
  calc
    _ ≤ Real.exp (P η σ D R/50)+2*(p+1)*(C*σ^(205:ℕ)*Real.exp (P η σ D R/50)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpol (by positivity))
    _ = (1+2*(p+1)*C*σ^(205:ℕ))*Real.exp (P η σ D R/50) := by ring
    _ ≤ Real.exp (P η σ D R/10)*Real.exp (P η σ D R/50) :=
      mul_le_mul_of_nonneg_right (hcoef.trans hh) (Real.exp_nonneg _)
    _ = Real.exp (P η σ D R/10+P η σ D R/50) := (Real.exp_add ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_high_pair_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (k c : ℝ) (hk : 0≤k) (hc : 0 ≤ c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R p a : ℝ,Range η σ D R →
      0≤p → p≤k*σ → 0≤a → a ≤ c*σ*Real.exp (P η σ D R/50) →
      400+a*(100*p)^200≤Real.exp (P η σ D R/10) ∧
      p^2≤Real.exp (P η σ D R/10) := by
  have hC : 0<400+c*(100*k)^(200:ℕ) := by
    exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg hc (pow_nonneg (by positivity) _))
  have hab := eventually_power_absorption hη hη' (400+c*(100*k)^(200:ℕ)) 201 (1/20)
    hC (by norm_num) (by norm_num)
  have hpabs := eventually_power_absorption hη hη' (1+k^2) 2 (1/10)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hpabs] with σ hσ hab hpabs
  intro D R p a hr hp hphi ha hahi
  have hσ0 : 0≤σ := by linarith
  have hP : 0≤P η σ D R := (Real.rpow_nonneg hσ0 _).trans
    (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  have hE : 1≤Real.exp (P η σ D R/50) := Real.one_le_exp_iff.mpr (by positivity)
  constructor
  · have hpw : (100*p)^(200:ℕ)≤((100*k)*σ)^200 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h1 : 1≤σ^(201:ℕ)*Real.exp (P η σ D R/50) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hσ) hE
    have hh : (400+c*(100*k)^(200:ℕ))*σ^(201:ℕ)≤Real.exp (P η σ D R/20) := by
      have ht := hab D R hr
      rw [show σ^(201:ℝ)=σ^(201:ℕ) from Real.rpow_natCast σ 201] at ht
      simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (20⁻¹:ℝ)] using ht
    calc
      _ ≤ 400*(σ^(201:ℕ)*Real.exp (P η σ D R/50))+
          (c*σ*Real.exp (P η σ D R/50))*((100*k)*σ)^200 :=
        add_le_add (by linarith) (mul_le_mul hahi hpw (pow_nonneg (by positivity) _) (by positivity))
      _ = ((400+c*(100*k)^(200:ℕ))*σ^(201:ℕ))*Real.exp (P η σ D R/50) := by ring
      _ ≤ Real.exp (P η σ D R/20)*Real.exp (P η σ D R/50) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
      _ = Real.exp (P η σ D R/20+P η σ D R/50) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hh := hpabs D R hr
    rw [show σ^(2:ℝ)=σ^(2:ℕ) from Real.rpow_natCast σ 2] at hh
    calc
      _ ≤ (k*σ)^2 := pow_le_pow_left₀ hp hphi _
      _ ≤ (1+k^2)*σ^2 := by nlinarith [sq_nonneg σ]
      _ ≤ _ := by simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using hh

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometryScaleOrientedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

lemma geometryScale_oriented_lower {q : ℕ} {σ n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n) (hnhi : n≤10*Real.exp (5*σ/2)) :
    Real.exp (3*σ/2)/10≤geometryScale q n := by
  unfold geometryScale
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2)) :=
      mul_le_mul_of_nonneg_left hnhi (by positivity)
    _ = Real.exp (4*σ) := by
      rw [show (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2))=
        Real.exp (3*σ/2)*Real.exp (5*σ/2) by ring,←Real.exp_add]
      congr 1
      ring
    _ = (q:ℝ)^4 := by rw [hq,←Real.exp_nat_mul]; norm_num

lemma high_strong_scale {q : ℕ} {σ n P p : ℝ} (hσ : 20000000≤σ)
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n) (hnhi : n≤10*Real.exp (5*σ/2))
    (hP : P≤σ/10) (hp : 0<p) (hp2 : p^2≤Real.exp (P/10)) :
    2≤geometryScale q n*Real.exp (-P) ∧
    16*((q:ℝ)+1)≤(geometryScale q n*Real.exp (-P))*(1/(100*p))^2 := by
  have hσ0 : 0≤σ := by linarith
  have hBlo := geometryScale_oriented_lower hq hn hnhi
  have hB : Real.exp (3*σ/2-P)/10≤geometryScale q n*Real.exp (-P) := by
    calc
      _ = (Real.exp (3*σ/2)/10)*Real.exp (-P) := by rw [Real.exp_sub,Real.exp_neg]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBlo (Real.exp_nonneg _)
  have hlarge : (3200000:ℝ)≤Real.exp (σ/4) := by
    linarith [Real.add_one_le_exp (σ/4)]
  have hq1 : 1≤(q:ℝ) := by rw [hq]; exact Real.one_le_exp_iff.mpr hσ0
  constructor
  · apply le_trans _ hB
    have he := Real.add_one_le_exp (3*σ/2-P)
    linarith
  · rw [div_pow,one_pow,mul_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0<100*p))).mpr
    apply le_trans _ hB
    calc
      _ ≤ 320000*(q:ℝ)*p^2 := by nlinarith [sq_nonneg p]
      _ ≤ 320000*Real.exp σ*Real.exp (P/10) := by rw [hq]; gcongr
      _ = 320000*Real.exp (σ+P/10) := by simp only [Real.exp_add]; ring
      _ ≤ (Real.exp (σ/4)/10)*Real.exp (σ+P/10) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = Real.exp (σ/4+σ+P/10)/10 := by simp only [Real.exp_add]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

open Filter ParameterHierarchy
open scoped Topology

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma momentOrder_bounds {σ P : ℝ} (hσ : 1≤σ) (hP : 1≤P) :
    Even (momentOrder σ P) ∧ 0 < momentOrder σ P ∧
      10000*σ/P≤(momentOrder σ P:ℝ) ∧ (momentOrder σ P:ℝ)≤10000*σ/P+2 ∧
      (momentOrder σ P:ℝ)≤10002*σ := by
  have hσ0 : 0<σ := by linarith
  have hP0 : 0<P := by linarith
  have hlo := Nat.le_ceil (5000*σ/P)
  have hhi := Nat.ceil_lt_add_one (by positivity : 0≤5000*σ/P)
  have hn : 0<⌈5000*σ/P⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hdiv : 5000*σ/P≤5000*σ := div_le_self (by positivity) hP
  have heq : 10000*σ/P = 2*(5000*σ/P) := by ring
  unfold momentOrder
  push_cast
  rw [heq]
  refine ⟨even_two_mul _,by omega,?_,?_,?_⟩ <;> linarith

lemma residualOrder_bound {σ : ℝ} (hσ : 1≤σ) :
    0 < residualOrder σ ∧ (residualOrder σ:ℝ)≤1000*Real.log σ+2 ∧
      (residualOrder σ:ℝ)≤1002*σ ∧
      (19/20:ℝ)^(residualOrder σ-1)≤σ^(-50:ℝ) := by
  have hσ0 : 0<σ := by linarith
  have hlog := Real.log_nonneg hσ
  have hhi := Nat.ceil_lt_add_one (show 0≤1000*Real.log σ by positivity)
  have hlo := Nat.le_ceil (1000*Real.log σ)
  have he : (19/20:ℝ)≤Real.exp (-(1/20:ℝ)) := by linarith [Real.add_one_le_exp (-(1/20:ℝ))]
  refine ⟨by unfold residualOrder; omega,?_,?_,?_⟩
  · unfold residualOrder
    push_cast
    linarith
  · have hl := Real.log_le_sub_one_of_pos hσ0
    unfold residualOrder
    push_cast
    linarith
  · simp only [residualOrder,Nat.add_sub_cancel]
    calc
      _ ≤ (Real.exp (-(1/20:ℝ)))^⌈1000*Real.log σ⌉₊ := pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp ((⌈1000*Real.log σ⌉₊:ℝ)*(-(1/20:ℝ))) := (Real.exp_nat_mul ..).symm
      _ ≤ Real.exp (Real.log σ*(-50)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := (Real.rpow_def_of_pos hσ0 _).symm

theorem eventually_moment_orders {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ D : ℝ,∀ R : ℕ,Range η σ D R →
      Even (momentOrder σ (P η σ D R)) ∧ 0 < momentOrder σ (P η σ D R) ∧
      10000*σ/P η σ D R≤(momentOrder σ (P η σ D R):ℝ) ∧
      (momentOrder σ (P η σ D R):ℝ)≤10000*σ/P η σ D R+2 ∧
      (momentOrder σ (P η σ D R):ℝ)≤10002*σ ∧
      200≤R/2 ∧ 0 < residualOrder σ ∧ residualOrder σ≤(R/2-5000)/(2*200) ∧
      (momentOrder σ (P η σ D R):ℝ)*(residualOrder σ:ℝ)*
        (19/20:ℝ)^(residualOrder σ-1)<1/2 := by
  have hb : 0<ParameterHierarchy.beta η := beta_pos hη
  have hlog := (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
  have ht : Tendsto (fun σ : ℝ => (1000000*Real.log σ+2000)/σ^(ParameterHierarchy.beta η)) atTop (𝓝 0) := by
    simpa only [add_div,mul_div_assoc,mul_zero,zero_add] using
      (hlog.const_mul 1000000).add ((tendsto_const_nhds (x:=(2000:ℝ))).div_atTop (tendsto_rpow_atTop hb))
  have hp : Tendsto (fun σ : ℝ => (10002*1002:ℝ)*σ^(-48:ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<48)).const_mul (10002*1002)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const (by norm_num : (0:ℝ)<1),
    hp.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (50000:ℝ))]
    with σ hσ ht hp hRlo
  intro D R hr
  have hσ0 : 0<σ := by linarith
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow hσ (by linarith : 0≤10*ParameterHierarchy.beta η)).trans
      (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  obtain ⟨heven,hpos,hplo,hphi,hps⟩ := momentOrder_bounds hσ hP
  obtain ⟨hhpos,hhlog,hhs,hpow⟩ := residualOrder_bound hσ
  have hsize : 1000*(residualOrder σ:ℝ)≤(R:ℝ) := by
    have hlog' := (div_le_iff₀ (Real.rpow_pos_of_pos hσ0 _)).mp ht.le
    nlinarith [hr.rlo]
  have hR : 50000≤R := by exact_mod_cast hRlo.trans hr.rlo
  have hsN : 1000*residualOrder σ≤R := by exact_mod_cast hsize
  have hsizeN : residualOrder σ≤(R/2-5000)/(2*200) := by omega
  refine ⟨heven,hpos,hplo,hphi,hps,by omega,hhpos,hsizeN,?_⟩
  apply lt_of_le_of_lt _ hp
  calc
    _ ≤ (10002*σ)*(1002*σ)*σ^(-50:ℝ) :=
      mul_le_mul (mul_le_mul hps hhs (Nat.cast_nonneg _) (by positivity)) hpow
        (pow_nonneg (by norm_num) _) (by positivity)
    _ = (10002*1002:ℝ)*σ^(-48:ℝ) := by
      rw [show (10002*σ)*(1002*σ)=(10002*1002:ℝ)*σ^(2:ℝ) by rw [Real.rpow_two]; ring,
        mul_assoc,←Real.rpow_add hσ0]
      norm_num

end

open Filter ParameterHierarchy
open scoped Topology

lemma pencilAlphabet_le {q k : ℕ} (hq : 1≤q) :
    (pencilAlphabet q k:ℝ)≤(k:ℝ)*(q:ℝ)^(k-1) := by
  unfold pencilAlphabet
  simp only [Nat.cast_sum,Nat.cast_pow]
  calc
    _ ≤ ∑ i∈Finset.range k,(q:ℝ)^(k-1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_right₀ (by exact_mod_cast hq)
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

lemma exp_geometryScale {q : ℕ} {σ g n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g)) :
    geometryScale q n=Real.exp (2*σ-g) := by
  rw [geometryScale,hq,hn,←Real.exp_nat_mul,←Real.exp_sub]
  congr 1
  norm_num
  ring

lemma exp_radialScale {q : ℕ} {σ g n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g)) :
    (q:ℝ)^4/n^2=Real.exp (-2*g) := by
  rw [hq,hn,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_sub]
  congr 1
  norm_num
  ring

lemma localTruncConstant_pos : 0<localTruncConstant := by
  exact mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _))
    (pow_pos (by norm_num) _)

lemma high_local_radial_numeric {q m : ℕ} {σ g n χ P M : ℝ}
    (hσ : 1≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hP : 0≤P) (hM : 0≤M) (hMhi : M≤8*Real.exp (-g))
    (hm : (m:ℝ)≤Real.exp (3*σ)) :
    (pencilAlphabet q 3:ℝ)*P^5000*
      (M^4900*(2^200*((Nat.clog 2 m:ℝ)+1)*((q:ℝ)^4/n^2*Real.exp χ))) ≤
      geometryScale q n*(localTruncConstant*σ*P^5000*Real.exp (χ-4901*g)) := by
  have hq1 : 1≤q := by
    have h := hq▸Real.one_le_exp_iff.mpr (show 0≤σ by linarith)
    exact_mod_cast h
  have hQ := pencilAlphabet_le (k:=3) hq1
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hQ
  have hq2 : (q:ℝ)^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul]; norm_num
  rw [hq2] at hQ
  have hdy := dyad_count_le hσ hm
  rw [exp_radialScale hq hn]
  calc
    _ ≤ (3*Real.exp (2*σ))*P^5000*
      ((8*Real.exp (-g))^4900*(2^200*(8*σ)*(Real.exp (-2*g)*Real.exp χ))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hQ (pow_nonneg hP _)) _ (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hM hMhi _) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdy (pow_nonneg (by norm_num) _)) (by positivity)
    _ = _ := by
      rw [exp_geometryScale hq hn,mul_pow,←Real.exp_nat_mul]
      simp only [Nat.cast_ofNat]
      rw [show (3*Real.exp (2*σ))*P^5000*(8^(4900:ℕ)*Real.exp (4900*(-g))*
          (2^(200:ℕ)*(8*σ)*(Real.exp (-2*g)*Real.exp χ))) =
        (24*2^(200:ℕ)*8^(4900:ℕ))*σ*P^5000*
          (Real.exp (2*σ)*Real.exp (4900*(-g))*Real.exp (-2*g)*Real.exp χ) by
            rw [show (24:ℝ)=3*8 by norm_num]; ac_rfl]
      rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
      unfold localTruncConstant
      rw [show Real.exp (2*σ-g)*((24*2^(200:ℕ)*8^(4900:ℕ))*σ*P^5000*Real.exp (χ-4901*g)) =
        (24*2^(200:ℕ)*8^(4900:ℕ))*σ*P^5000*(Real.exp (2*σ-g)*Real.exp (χ-4901*g)) by ac_rfl]
      rw [←Real.exp_add]
      congr 2
      ring

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_Aggregate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma poisson_zero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hasLaw_coordinate (rate : ι→ℝ≥0) (i : ι) :
    HasLaw (fun ω : ι→ℕ => ω i) (poissonMeasure (rate i)) (batchMeasure rate) :=
  (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw

omit [DecidableEq ι] in
lemma coordinate_independent (rate : ι→ℝ≥0) :
    iIndepFun (fun i (ω : ι→ℕ) => ω i) (batchMeasure rate) := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma hasLaw_sum (rate : ι→ℝ≥0) (s : Finset ι) :
    HasLaw (fun ω : ι→ℕ => ∑ i∈s,ω i) (poissonMeasure (∑ i∈s,rate i))
      (batchMeasure rate) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,poisson_zero]
    exact ⟨measurable_const.aemeasurable,by simp⟩
  | @insert i s hi ih =>
    have hind := (coordinate_independent rate).indepFun_finsetSum_of_notMem
      (fun j => measurable_pi_apply j) hi
    have he : (∑ j∈s,fun ω : ι→ℕ => ω j) = (fun ω => ∑ j∈s,ω j) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hind
    have h := hind.symm.hasLaw_add_poissonMeasure (hasLaw_coordinate rate i) ih
    change HasLaw (fun ω : ι→ℕ => ω i+∑ j∈s,ω j) _ _ at h
    simpa only [Finset.sum_insert hi] using h

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem measurePreserving_aggregate (label : ι→D) (rate : ι→ℝ≥0) :
    MeasurePreserving (aggregate label) (batchMeasure rate)
      (batchMeasure (aggregateRate label rate)) := by
  have hsum (d : D) : MeasurePreserving
      (fun ω : {i // label i=d}→ℕ => ∑ i,ω i)
      (batchMeasure (fun i : {i // label i=d} => rate i))
      (poissonMeasure (aggregateRate label rate d)) := by
    refine ⟨by fun_prop,?_⟩
    exact (hasLaw_sum (fun i : {i // label i=d} => rate i) Finset.univ).map_eq
  exact (measurePreserving_pi _ _ hsum).comp (measurePreserving_partition rate label)

omit [DecidableEq ι] [Fintype D] in
lemma emptyIndicator_aggregate (label : ι→D) (ω : ι→ℕ) (s : Finset D) :
    emptyIndicator s (aggregate label ω) =
      emptyIndicator (Finset.univ.filter fun i => label i∈s) ω := by
  have he : aggregate label ω∈emptyEvent s ↔
      ω∈emptyEvent (Finset.univ.filter fun i => label i∈s) := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      aggregate,Finset.sum_eq_zero_iff,forall_const,Finset.mem_univ,
      Finset.mem_filter,true_and]
    constructor
    · intro h i hi
      exact h (label i) hi ⟨i,rfl⟩
    · intro h d hd i
      exact h i (by simpa only [i.property] using hd)
  unfold emptyIndicator
  by_cases h : aggregate label ω∈emptyEvent s
  · simp [h,he.mp h]
  · simp [h,mt he.mpr h]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma measurePreserving_schedule_aggregate (label : ι→D) (rate : ι→ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ => fun r => aggregate label (ω r))
      (scheduleMeasure rate R) (scheduleMeasure (aggregateRate label rate) R) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_aggregate label rate)

omit [DecidableEq ι] [Fintype D] in
lemma scoreTerm_aggregate (label : ι→D) {R : ℕ} (s : Finset D) (b : ℝ)
    (own : Fin R→Bool) (ω : Fin R→ι→ℕ) :
    scoreTerm s b own (fun r => aggregate label (ω r)) =
      scoreTerm (Finset.univ.filter fun i => label i∈s) b own ω := by
  unfold scoreTerm centeredFactor
  simp_rw [emptyIndicator_aggregate]

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_TypicalScoreAggregate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [DecidableEq ι] [Fintype D] [Fintype H] in
lemma typicalScore_aggregate (label : ι→D) {R : ℕ} (s : Finset H)
    (lines : H→Finset D) (b : ℝ) (own : H→Fin R→Bool) (ω : Fin R→ι→ℕ) :
    typicalScore s lines b own (fun r => aggregate label (ω r)) =
      typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω := by
  unfold typicalScore
  simp_rw [scoreTerm_aggregate]

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma radialLabel_fiber_card (X : Finset {y : ℙ K V // x ≠ y}) (l : RadialLine x) :
    Fintype.card {y : X // radialLabel x X y=l}=(RadialLine.trainingOnLine X l).card := by
  rw [RadialLine.trainingOnLine_eq_fiber]
  change (Finset.univ : Finset {y : X // radialLabel x X y=l}).card=_
  apply Finset.card_bij (fun y _ => y.val.val)
  · intro y _
    exact Finset.mem_filter.mpr ⟨y.val.property,y.property⟩
  · intro y _ z _ he
    exact Subtype.ext (Subtype.ext he)
  · intro y hy
    obtain ⟨hyX,hyl⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨⟨y,hyX⟩,hyl⟩,Finset.mem_univ _,rfl⟩

omit [Fintype (RadialLine x)] in
lemma aggregateRate_radialLabel (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0) :
    aggregateRate (radialLabel x X) (fun _ => L*δ) =
      fun l => L*radialWeight x X δ l := by
  funext l
  simp only [aggregateRate,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    radialLabel_fiber_card,radialWeight]
  ring

omit [FiniteDimensional K V] in
lemma radialLabel_in_pencil (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) (y : X) :
    radialLabel x X y ∈ pencilLines x F H ↔ Incident y.val.val H.val := by
  simp only [radialLabel,pencilLines,RadialLine.inFlat,Finset.mem_filter,Finset.mem_univ,
    true_and,RadialLine.through_le_iff]
  change Incident x H.val ∧ Incident y.val.val H.val ↔ _
  simp only [hF H.val H.property,true_and]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PointStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma coe_pointStrength (S : Finset (ℙ K V)) :
    (pointStrength (K:=K) S:ℝ)=(Nat.card K:ℝ)/S.card := by
  simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_High
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open scoped BigOperators

lemma pencil_high_budget_ratios {q : ℕ} {σ n : ℝ} (hσ : 10≤σ)
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n) (hnhi : n≤10*Real.exp (5*σ/2)) :
    1≤geometryScale q n ∧
    (pencilAlphabet q 4:ℝ)/(geometryScale q n*(Real.exp (σ/5))^8)≤40 ∧
    (pencilAlphabet q 2:ℝ)*Real.exp (σ/5)/geometryScale q n≤20 ∧
    (pencilAlphabet q 4:ℝ)/(geometryScale q n)^2≤400 := by
  let B := geometryScale q n
  have hσ0 : 0≤σ := by linarith
  have hq1 : 1≤q := by
    have hh := hq▸Real.one_le_exp_iff.mpr hσ0
    exact_mod_cast hh
  have hBlo : Real.exp (3*σ/2)/10≤B := by
    unfold B geometryScale
    apply (le_div_iff₀ hn).mpr
    calc
      _ ≤ (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2)) :=
        mul_le_mul_of_nonneg_left hnhi (by positivity)
      _ = Real.exp (4*σ) := by
        rw [show (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2))=Real.exp (3*σ/2)*Real.exp (5*σ/2) by ring]
        rw [←Real.exp_add]
        congr 1
        ring
      _ = (q:ℝ)^4 := by rw [hq,←Real.exp_nat_mul]; norm_num
  have hB1 : 1≤B := by
    have he := Real.add_one_le_exp (3*σ/2)
    linarith
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB1
  have hQ : (pencilAlphabet q 4:ℝ)≤4*Real.exp (3*σ) := by
    have hh := pencilAlphabet_le (k:=4) hq1
    norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hh
    rw [hq,←Real.exp_nat_mul] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hN : (pencilAlphabet q 2:ℝ)≤2*Real.exp σ := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,hq] using pencilAlphabet_le (k:=2) hq1
  have hb8 : (Real.exp (σ/5))^8=Real.exp (8*σ/5) := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  refine ⟨hB1,?_,?_,?_⟩
  · apply (div_le_iff₀ (mul_pos hB0 (pow_pos (Real.exp_pos _) _))).mpr
    calc
      _ ≤ 4*Real.exp (3*σ) := hQ
      _ ≤ 4*Real.exp (3*σ/2+8*σ/5) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = 40*((Real.exp (3*σ/2)/10)*(Real.exp (σ/5))^8) := by
        rw [hb8,Real.exp_add]
        ring
      _ ≤ 40*(B*(Real.exp (σ/5))^8) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBlo (by positivity)) (by norm_num)
  · apply (div_le_iff₀ hB0).mpr
    calc
      _ ≤ (2*Real.exp σ)*Real.exp (σ/5) := mul_le_mul_of_nonneg_right hN (Real.exp_nonneg _)
      _ = 2*Real.exp (σ+σ/5) := by rw [mul_assoc,←Real.exp_add]
      _ ≤ 2*Real.exp (3*σ/2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = 20*(Real.exp (3*σ/2)/10) := by ring
      _ ≤ 20*B := mul_le_mul_of_nonneg_left hBlo (by norm_num)
  · apply (div_le_iff₀ (sq_pos_of_pos hB0)).mpr
    calc
      _ ≤ 4*Real.exp (3*σ) := hQ
      _ = 400*(Real.exp (3*σ/2)/10)^2 := by
        rw [div_pow,←Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show (2:ℝ)*(3*σ/2)=3*σ by ring]
        ring
      _ ≤ 400*B^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBlo 2) (by norm_num)

end

section
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_high_geometric_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q m : ℕ) (n D : ℝ) (R : ℕ),
      (q:ℝ)=Real.exp σ → 0<n →
      n≤10*Real.exp (5*σ/2) →
      (m:ℝ)≤Real.exp (3*σ) → Range η σ D R →
      let B := geometryScale q n
      let p := momentOrder σ (P η σ D R)
      let a := dyadFactor m (P η σ D R/100)
      10000≤L η σ D ∧
      (40*B*Real.exp (L η σ D/100)+B)+2*((p+1:ℝ)*
        highMomentBudget (pencilAlphabet q 4) (a*B^2) (a*B) B (Real.exp (σ/5))
          (L η σ D) p R (pencilAlphabet q 2))≤
        B*Real.exp (P η σ D R/5) ∧
      (pencilAlphabet q 4:ℝ)+(a*B^2)/(1/(100*(p:ℝ)))^200≤B^2*Real.exp (P η σ D R/10) ∧
      (p:ℝ)^2≤Real.exp (P η σ D R/10) ∧
      2≤B*Real.exp (-P η σ D R) ∧
      16*((q:ℝ)+1)≤(B*Real.exp (-P η σ D R))*(1/(100*(p:ℝ)))^2 := by
  let c : ℝ := 8*2^(200:ℕ)
  have hcost := eventually_high_poly_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hpairs := eventually_high_pair_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hhier := eventually_hierarchy hη hη' 0 (1/10) 10000 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (20000000:ℝ),hcost,hpairs,hhier] with σ hσ hc hp hh
  intro q m n D R hq hn hnor hm hr
  have hσ1 : 1≤σ := by linarith
  obtain ⟨hD,hR,hpow,hLlo,hLhi,hPlo,hPhi⟩ := finite_bounds hη hη' hσ1 hr
  have ht := hh D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
  have hL : 10000≤L η σ D := ht.1
  have hPσ : P η σ D R≤σ/10 := by simpa only [div_eq_mul_inv,one_mul,mul_comm (10⁻¹:ℝ)] using ht.2.1
  have hL0 : 0<L η σ D := by linarith
  have hR1 : 1≤(R:ℝ) := hpow.trans hr.rlo
  have hP1 : 1≤P η σ D R := by unfold P; nlinarith
  let B := geometryScale q n
  let p := momentOrder σ (P η σ D R)
  let a := dyadFactor m (P η σ D R/100)
  obtain ⟨_,hpos,_,_,hps⟩ := momentOrder_bounds hσ1 hP1
  have hrat := pencil_high_budget_ratios (by linarith) hq hn hnor
  have hB : 0<B := lt_of_lt_of_le zero_lt_one hrat.1
  have hB1 : 1≤B := hrat.1
  have ha : 0≤a := by dsimp [a,dyadFactor];positivity
  have has : a ≤ c*σ*Real.exp (P η σ D R/50) := dyadFactor_exp_bound hσ1 hm
  have hc' := hc D R p a hr
    (Nat.cast_nonneg _) hps ha has
  have hp' := hp D R p a hr (Nat.cast_nonneg _) hps ha has
  have hbudget := highMomentBudget_le_poly (pencilAlphabet q 4) a B (Real.exp (σ/5))
    (L η σ D) p R (pencilAlphabet q 2) hB1 (Real.exp_pos _) ha hL0.le
    hrat.2.1 hrat.2.2.1 hrat.2.2.2
  have hPL : (R:ℝ)*L η σ D=P η σ D R := by unfold P;ring
  rw [hPL] at hbudget
  have hsingleton : (40*Real.exp (L η σ D/100)+1)≤Real.exp (P η σ D R/50) := by
    have h40 : (41:ℝ)≤Real.exp (L η σ D/100) := by linarith [Real.add_one_le_exp (L η σ D/100)]
    calc
      _ ≤ 41*Real.exp (L η σ D/100) := by
        have he := Real.one_le_exp_iff.mpr (by positivity : 0≤L η σ D/100)
        linarith
      _ ≤ Real.exp (L η σ D/100)*Real.exp (L η σ D/100) := mul_le_mul_of_nonneg_right h40 (Real.exp_nonneg _)
      _ = Real.exp (L η σ D/50) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold P;nlinarith)
  refine ⟨hL,?_,?_,hp'.2,high_strong_scale hσ hq hn hnor hPσ (Nat.cast_pos.mpr hpos) hp'.2⟩
  · calc
      _ ≤ B*Real.exp (P η σ D R/50)+2*((p+1:ℝ)*(B*highBudgetPoly a p (P η σ D R))) := by
        apply add_le_add
        · nlinarith only [mul_le_mul_of_nonneg_left hsingleton hB.le]
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (by positivity)) (by norm_num)
      _ = B*(Real.exp (P η σ D R/50)+2*(p+1)*highBudgetPoly a p (P η σ D R)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' hB.le
  · have htpos : 0<1/(100*(p:ℝ)) := by positivity
    have hQ : (pencilAlphabet q 4:ℝ)≤400*B^2 := (div_le_iff₀ (sq_pos_of_pos hB)).mp hrat.2.2.2
    calc
      _ = (pencilAlphabet q 4:ℝ)+B^2*(a*(100*(p:ℝ))^200) := by rw [div_pow,one_pow];field_simp;ring
      _ ≤ 400*B^2+B^2*(a*(100*(p:ℝ))^200) := add_le_add hQ (le_refl _)
      _ = B^2*(400+a*(100*(p:ℝ))^200) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp'.1 (sq_nonneg _)

end
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open ProjectiveTraining GlobalRadial WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePreservingSplitSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurePreserving_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ =>
      ((fun r (i : {i // p i}) => ω r i),(fun r (i : {i // ¬p i}) => ω r i)))
      (scheduleMeasure rate R)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
  have h1 := measurePreserving_pi (fun _ : Fin R => batchMeasure rate)
    (fun _ : Fin R => (batchMeasure (fun i : {i // p i} => rate i)).prod
      (batchMeasure (fun i : {i // ¬p i} => rate i)))
    (fun _ => measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) p)
  exact (measurePreserving_arrowProdEquivProdArrow ({i // p i}→ℕ) ({i // ¬p i}→ℕ)
    (Fin R) (fun _ => batchMeasure (fun i : {i // p i} => rate i))
      (fun _ => batchMeasure (fun i : {i // ¬p i} => rate i))).comp h1

omit [DecidableEq ι] in
lemma integral_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    {R : ℕ} (F : (Fin R→{i // p i}→ℕ)→(Fin R→{i // ¬p i}→ℕ)→ℝ)
    (M : ℝ) (hM : ∀ u v,|F u v|≤M) :
    (∫ ω,F (fun r i => ω r i) (fun r i => ω r i) ∂scheduleMeasure rate R) =
      ∫ u,∫ v,F u v ∂scheduleMeasure (fun i : {i // ¬p i} => rate i) R
        ∂scheduleMeasure (fun i : {i // p i} => rate i) R := by
  let μ := scheduleMeasure (fun i : {i // p i} => rate i) R
  let ν := scheduleMeasure (fun i : {i // ¬p i} => rate i) R
  let G : (Fin R→{i // p i}→ℕ)×(Fin R→{i // ¬p i}→ℕ)→ℝ := fun z => F z.1 z.2
  have hG : Integrable G (μ.prod ν) := by
    apply Integrable.of_bound (measurable_of_countable G).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ = ∫ z,G z ∂μ.prod ν :=
      (measurePreserving_split_schedule rate p R).hasLaw.integral_comp
        (measurable_of_countable G).aestronglyMeasurable
    _ = _ := integral_prod G hG

omit [DecidableEq ι] in
lemma integral_split_schedule_le (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    {R : ℕ} (F : (Fin R→{i // p i}→ℕ)→(Fin R→{i // ¬p i}→ℕ)→ℝ)
    (M B : ℝ) (hM : ∀ u v,|F u v|≤M)
    (hB : ∀ u,(∫ v,F u v ∂scheduleMeasure (fun i : {i // ¬p i} => rate i) R)≤B) :
    (∫ ω,F (fun r i => ω r i) (fun r i => ω r i) ∂scheduleMeasure rate R)≤B := by
  rw [integral_split_schedule rate p F M hM]
  have hG : Integrable (fun z : (Fin R→{i // p i}→ℕ)×(Fin R→{i // ¬p i}→ℕ) => F z.1 z.2)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ ≤ ∫ _u : Fin R→{i // p i}→ℕ,B ∂scheduleMeasure (fun i : {i // p i} => rate i) R :=
      integral_mono hG.integral_prod_left (integrable_const B) hB
    _ = B := by simp

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AbsScoreTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [Fintype ι] [DecidableEq ι] in
lemma abs_scoreTerm_le_one {R : ℕ} (s : Finset ι) {b : ℝ}
    (hb : b∈Set.Icc 0 1) (own : Fin R→Bool) (ω : Fin R→ι→ℕ) :
    |scoreTerm s b own ω|≤1 := by
  unfold scoreTerm
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro r _
  split_ifs
  · exact abs_centeredFactor_le_one s b hb _
  · simp

omit [Fintype ι] [DecidableEq ι] [Fintype H] in
lemma abs_typicalScore_le_card {R : ℕ} (F : Finset H) (lines : H→Finset ι)
    {b : ℝ} (hb : b∈Set.Icc 0 1) (own : H→Fin R→Bool) (ω : Fin R→ι→ℕ) :
    |typicalScore F lines b own ω|≤F.card := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    (∑ h∈F,|scoreTerm (lines h) b (own h) ω|)≤∑ _h∈F,(1:ℝ) :=
      Finset.sum_le_sum fun h _ => abs_scoreTerm_le_one (lines h) hb (own h) ω
    _ = _ := by simp

omit [DecidableEq ι] [DecidableEq D] in
lemma measurePreserving_schedule_reindex (e : ι≃D) (rate : D→ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ => fun r d => ω r (e.symm d))
      (scheduleMeasure (fun i => rate (e i)) R) (scheduleMeasure rate R) := by
  have h := measurePreserving_pi (fun _ : Fin R => batchMeasure (fun i => rate (e i)))
    (fun _ : Fin R => batchMeasure rate) (fun _ => measurePreserving_piCongrLeft
    (fun d => poissonMeasure (rate d)) e)
  convert h using 1 <;> try rfl
  funext ω r d
  simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

omit [DecidableEq ι] [DecidableEq D] in
lemma integral_schedule_reindex (e : ι≃D) (rate : D→ℝ≥0) {R : ℕ}
    (F : (Fin R→D→ℕ)→ℝ) :
    (∫ ω,F (fun r d => ω r (e.symm d)) ∂scheduleMeasure (fun i => rate (e i)) R) =
      ∫ ω,F ω ∂scheduleMeasure rate R :=
  (measurePreserving_schedule_reindex e rate R).hasLaw.integral_comp
    (measurable_of_countable F).aestronglyMeasurable

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalUniformWeightedScoreMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [DecidableEq ι] [DecidableEq D] [Fintype H] in
theorem original_uniform_weighted_score_moment (p : ι→Prop) [DecidablePred p]
    (e : {i // ¬p i}≃D) (rate : ℝ≥0) {R : ℕ}
    (F : Finset H) (lines : H→Finset D) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (own : (Fin R→{i // p i}→ℕ)→H→Fin R→Bool)
    (g : (Fin R→D→ℕ)→ℝ) (hg : ∀v,|g v|≤1) (k : ℕ) (B : ℝ)
    (hB : ∀u,(∫ v,g v*(typicalScore F lines b (own u) v)^k
      ∂scheduleMeasure (fun _ : D => rate) R)≤B) :
    (∫ ω,g (fun r d => ω r (e.symm d).val)*
      (typicalScore F lines b (own (fun r i => ω r i))
        (fun r d => ω r (e.symm d).val))^k ∂scheduleMeasure (fun _ : ι => rate) R)≤B := by
  apply integral_split_schedule_le (fun _ : ι => rate) p
    (fun u v => g (fun r d => v r (e.symm d))*
      (typicalScore F lines b (own u) (fun r d => v r (e.symm d)))^k)
    ((F.card:ℝ)^k) B
  · intro u v
    rw [abs_mul,abs_pow]
    exact (mul_le_mul (hg _) (pow_le_pow_left₀ (abs_nonneg _)
      (abs_typicalScore_le_card F lines hb (own u) _) k) (pow_nonneg (abs_nonneg _) _)
      (by norm_num)).trans_eq (one_mul _)
  · intro u
    rw [integral_schedule_reindex e (fun _ : D => rate)
      (fun v => g v*(typicalScore F lines b (own u) v)^k)]
    exact hB u

omit [Fintype H] in
lemma integral_original_weighted_score_pow (label : ι→D) (rate : ι→ℝ≥0)
    {R : ℕ} (s : Finset H) (lines : H→Finset D) (b : ℝ)
    (own : H→Fin R→Bool) (p : ℕ) (g : (Fin R→D→ℕ)→ℝ) :
    (∫ ω,g (fun r => aggregate label (ω r))*
      (typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω)^p
      ∂scheduleMeasure rate R) =
    ∫ ω,g ω*(typicalScore s lines b own ω)^p ∂scheduleMeasure (aggregateRate label rate) R := by
  simp_rw [←typicalScore_aggregate label s lines b own]
  exact (measurePreserving_schedule_aggregate label rate R).hasLaw.integral_comp
    (measurable_of_countable (fun ω : Fin R→D→ℕ =>
      g ω*(typicalScore s lines b own ω)^p)).aestronglyMeasurable

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OwnQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
theorem modifiedPointScore_eq (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ)
    (hω : Unsampled x S ω) : modifiedPointScore x S O F b ω=pointScore S O F b ω := by
  unfold modifiedPointScore typicalScore pointScore
  apply Finset.sum_congr rfl
  intro H hH
  unfold scoreTerm
  apply Finset.prod_congr rfl
  intro r hr
  have ho : (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → ω r y=0) ↔
      (∀ y : S,y.val∈O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI
      by_cases hx : x=y.val
      · exact hω r y hx
      · exact h y hy hx hI
    · intro h y hy _ hI
      exact h y hy hI
  have he : (fun d : outsideAt x S O => ω r ((outsideEquiv x S O).symm d).val) ∈
      emptyEvent (Finset.univ.filter fun y : outsideAt x S O => Incident y.val.val H.val) ↔
      (∀ y : S,y.val∉O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI
      by_cases hx : x=y.val
      · exact hω r y hx
      · let z : {y : S // ¬ownQuery x S O y} := ⟨y,not_or.mpr ⟨hy,hx⟩⟩
        have hz : (outsideEquiv x S O z)∈Finset.univ.filter
            (fun y : outsideAt x S O => Incident y.val.val H.val) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI⟩
        have hh := h (outsideEquiv x S O z) hz
        simpa only [Equiv.symm_apply_apply,Set.mem_singleton_iff] using hh
    · intro h y hy
      apply h ((outsideEquiv x S O).symm y).val
      · exact (not_or.mp ((outsideEquiv x S O).symm y).property).1
      · exact (Finset.mem_filter.mp hy).2
  change (if decide (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → ω r y=0)
    then _ else 0)=_
  simp only [ho,decide_eq_true_eq,centeredFactor,emptyIndicator,Set.indicator_apply,he]
  split_ifs <;> ring

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ModifiedRadialSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
lemma original_weighted_radial_moment (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    (b : ℝ) (own : F→Fin R→Bool) (p : ℕ) (g : (Fin R→RadialLine x→ℕ)→ℝ) :
    (∫ ω,g (fun r => aggregate (radialLabel x X) (ω r))*
      (typicalScore Finset.univ
        (fun H : F => Finset.univ.filter fun y : X => Incident y.val.val H.val) b own ω)^p
      ∂scheduleMeasure (fun _ : X => L*δ) R) =
    ∫ ω,g ω*(typicalScore Finset.univ (pencilLines x F) b own ω)^p
      ∂scheduleMeasure (fun l => L*radialWeight x X δ l) R := by
  have h := integral_original_weighted_score_pow (radialLabel x X) (fun _ => L*δ)
    Finset.univ (pencilLines x F) b own p g
  simp_rw [radialLabel_in_pencil x X F hF,aggregateRate_radialLabel] at h
  exact h

omit [Finite K] in
theorem actual_original_weighted (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b : ℝ} (hb : b∈Set.Icc 0 1) (p : ℕ) (g : (Fin R→RadialLine x→ℕ)→ℝ)
    (hg : ∀ω,|g ω|≤1) (B : ℝ)
    (hB : ∀own : F→Fin R→Bool,
      (∫ ω,g ω*(typicalScore Finset.univ (pencilLines x F) b own ω)^p
        ∂scheduleMeasure (fun l => L*radialWeight x (outsideAt x S O) δ l) R)≤B) :
    (∫ ω,g (modifiedRadialSchedule x S O ω)*(modifiedPointScore x S O F b ω)^p
      ∂scheduleMeasure (fun _ : S => L*δ) R)≤B := by
  apply original_uniform_weighted_score_moment (ownQuery x S O) (outsideEquiv x S O)
    (L*δ) Finset.univ _ hb (ownBitsMinus x S O F)
    (fun v => g (fun r => aggregate (radialLabel x (outsideAt x S O)) (v r)))
    (fun v => hg _) p B
  intro u
  rw [original_weighted_radial_moment x (outsideAt x S O) L δ F hF]
  exact hB _

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem measurePreserving_modifiedRadial (S O : Finset (ℙ K V)) (L δ : ℝ≥0) (R : ℕ) :
    MeasurePreserving (modifiedRadialSchedule x S O (R:=R))
      (scheduleMeasure (fun _ : S => L*δ) R)
      (scheduleMeasure (fun l => L*radialWeight x (outsideAt x S O) δ l) R) := by
  have hsplit := measurePreserving_split_schedule (fun _ : S => L*δ) (ownQuery x S O) R
  have hproj := (measurePreserving_snd (μ:=scheduleMeasure
    (fun _ : {y : S // ownQuery x S O y} => L*δ) R)
    (ν:=scheduleMeasure (fun _ : {y : S // ¬ownQuery x S O y} => L*δ) R)).comp hsplit
  have hr := (measurePreserving_schedule_reindex (outsideEquiv x S O)
    (fun _ : outsideAt x S O => L*δ) R).comp hproj
  have ha := (measurePreserving_schedule_aggregate (radialLabel x (outsideAt x S O))
    (fun _ : outsideAt x S O => L*δ) R).comp hr
  rw [aggregateRate_radialLabel] at ha
  exact ha

omit [Finite K] in
theorem original_truncation_failure (S O : Finset (ℙ K V)) (L δ : ℝ≥0) (R J : ℕ) :
    (∫ω,1-HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))
      ∂scheduleMeasure (fun _ : S => L*δ) R) =
    ∫ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun p : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ p.2) := by
  exact ((measurePreserving_uncurry_schedule
    (fun l => L*radialWeight x (outsideAt x S O) δ l) R).comp
      (measurePreserving_modifiedRadial x S O L δ R)).hasLaw.integral_comp
        (measurable_of_countable (fun ω => 1-HighMoment.allTrunc R J ω)).aestronglyMeasurable

omit [Finite K] in
theorem original_truncated_moment (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b : ℝ} (hb : b∈Set.Icc 0 1) (p J : ℕ) (B : ℝ)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (∫ω,HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))*
      (modifiedPointScore x S O F b ω)^p ∂scheduleMeasure (fun _ : S => L*δ) R)≤B := by
  apply actual_original_weighted x S O L δ F hF hb p
    (fun ω => HighMoment.allTrunc R J (Function.uncurry ω))
    (fun ω => by rw [abs_of_nonneg (HighMoment.allTrunc_range R J _).1]
                 exact (HighMoment.allTrunc_range R J _).2) B
  intro own
  have he := (measurePreserving_uncurry_schedule
    (fun l => L*radialWeight x (outsideAt x S O) δ l) R).hasLaw.integral_comp
      (measurable_of_countable (fun ω : Fin R×RadialLine x→ℕ => HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p)).aestronglyMeasurable
  exact he.trans_le (hB own)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_FailureCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω X : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

theorem weighted_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω→ℝ) {M t B : ℝ} (hf : ∀ω,|f ω|≤M) (hg : ∀ω,g ω∈Set.Icc 0 1)
    {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,g ω*(f ω)^p ∂μ)≤B) :
    μ.real {ω | g ω=1 ∧ t < |f ω|}≤B/t^p := by
  have hi : Integrable (fun ω => g ω*(f ω)^p) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (M^p)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hg ω).1,abs_pow]
      exact (mul_le_mul (hg ω).2 (pow_le_pow_left₀ (abs_nonneg _) (hf ω) p)
        (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq (one_mul _)
  have hnn : ∀ω,0≤g ω*(f ω)^p := fun ω => mul_nonneg (hg ω).1 (hp.pow_nonneg _)
  have hsub : {ω | g ω=1 ∧ t < |f ω|}⊆{ω | t^p≤g ω*(f ω)^p} := by
    intro ω hω
    change t^p≤g ω*(f ω)^p
    rw [hω.1,one_mul,←hp.pow_abs (f ω)]
    exact pow_le_pow_left₀ ht.le hω.2.le p
  apply (le_div_iff₀ (pow_pos ht p)).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
    (pow_nonneg ht.le p)).trans ((mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hnn) hi (t^p)).trans hB)

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

theorem truncated_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω→ℝ) {M t B : ℝ} (hf : ∀ω,|f ω|≤M) (hg : ∀ω,g ω=0 ∨ g ω=1)
    {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,g ω*(f ω)^p ∂μ)≤B) :
    μ.real {ω | t < |f ω|}≤B/t^p+(∫ω,1-g ω ∂μ) := by
  have hgr : ∀ω,g ω∈Set.Icc 0 1 := fun ω => by rcases hg ω with h|h <;> simp [h]
  have h1 := weighted_moment_tail μ f g hf hgr hp ht hB
  have hi : (∫ω,1-g ω ∂μ)=μ.real {ω | g ω=0} := by
    have he : (fun ω => 1-g ω)=({ω | g ω=0}).indicator (fun _ => (1:ℝ)) := by
      funext ω
      rcases hg ω with h|h <;> simp [h]
    rw [he,integral_indicator_const (1:ℝ) (Set.to_countable _ |>.measurableSet)]
    simp
  have hs : {ω | t < |f ω|}⊆{ω | g ω=1 ∧ t < |f ω|}∪{ω | g ω=0} := by
    intro ω hω
    rcases hg ω with h|h
    · exact Or.inr h
    · exact Or.inl ⟨h,hω⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
    (by rw [hi];exact add_le_add h1 (le_refl _))

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_IntegralForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory PoissonScore TupleComponents
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma allTrunc_indicator (R J : ℕ) (ω : Fin R→D→ℕ) :
    1-allTrunc R J (Function.uncurry ω) =
      (overloaded Finset.univ J).indicator (fun _ => (1:ℝ)) ω := by
  by_cases he : ω∈(overloaded Finset.univ J : Set (Fin R→D→ℕ))
  · rw [Set.indicator_of_mem he]
    obtain ⟨d,_,hd⟩ := he
    have hz : allTrunc R J (Function.uncurry ω)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      exact ite_eq_right (by exact not_lt.mpr hd)
    rw [hz,sub_zero]
  · rw [Set.indicator_of_notMem he]
    have ho : allTrunc R J (Function.uncurry ω)=1 := by
      apply Finset.prod_eq_one
      intro d _
      apply ite_eq_left
      by_contra hn
      exact he ⟨d,Finset.mem_univ _,le_of_not_gt hn⟩
    rw [ho,sub_self]

end SharpRamseyFive.HighMoment

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AbsModifiedPointScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] [FiniteDimensional K V] [Fintype (RadialLine x)] in
lemma abs_modifiedPointScore (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} {b : ℝ} (hb : b∈Set.Icc 0 1)
    (ω : Fin R→S→ℕ) : |modifiedPointScore x S O F b ω|≤F.card := by
  simpa only [Finset.card_univ,Fintype.card_coe,modifiedPointScore] using
    abs_typicalScore_le_card Finset.univ _ hb
      (ownBitsMinus x S O F (fun r i => ω r i))
      (fun r d => ω r ((outsideEquiv x S O).symm d).val)

omit [Finite K] in
theorem unsampled_score_tail (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b t B : ℝ} (hb : b∈Set.Icc 0 1) {p J : ℕ} (hp : Even p) (ht : 0<t)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (scheduleMeasure (fun _ : S => L*δ) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|} ≤ B/t^p+
    ∫ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2) := by
  have hbound := original_truncated_moment x S O L δ F hF hb p J B hB
  have hg : ∀ω : Fin R→S→ℕ,
      HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))=0 ∨
      HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))=1 := by
    intro ω
    have hi := HighMoment.allTrunc_indicator R J (modifiedRadialSchedule x S O ω)
    by_cases he : modifiedRadialSchedule x S O ω∈overloaded Finset.univ J
    · rw [Set.indicator_of_mem he] at hi
      exact Or.inl (by linarith only [hi])
    · rw [Set.indicator_of_notMem he] at hi
      exact Or.inr (by linarith only [hi])
  have h := truncated_moment_tail (scheduleMeasure (fun _ : S => L*δ) R)
    (modifiedPointScore x S O F b)
    (fun ω => HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω)))
    (abs_modifiedPointScore x S O F hb) hg hp ht hbound
  rw [original_truncation_failure] at h
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*δ) R) ?_ (measure_ne_top _ _)).trans h
  intro ω hω
  change t < |modifiedPointScore x S O F b ω|
  rw [modifiedPointScore_eq x S O F b ω hω.1]
  exact hω.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MomentTailRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma moment_tail_ratio {B κ α P : ℝ} (hB : 0<B) (p : ℕ) :
    (B^p*Real.exp (-α*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p =
      Real.exp ((p:ℝ)*(κ+Real.log 10-α*P)) := by
  have ht : B*Real.exp (-κ)/10=B*Real.exp (-(κ+Real.log 10)) := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 10),Real.exp_log (by norm_num : (0:ℝ)<10)]
    ring
  rw [ht,mul_pow,←Real.exp_nat_mul]
  have he : -α*((p:ℝ)*P)=((p:ℝ)*(κ+Real.log 10-α*P))+(p:ℝ)*(-(κ+Real.log 10)) := by ring
  rw [he,Real.exp_add]
  field_simp

lemma high_tail_ratio {B κ P : ℝ} (hB : 0<B)
    (p : ℕ) (hκ : κ+Real.log 10≤P/20) :
    (B^p*Real.exp (-(1/10:ℝ)*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p≤
      Real.exp (-((p:ℝ)*P)/20) := by
  rw [moment_tail_ratio hB p]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hκ (Nat.cast_nonneg p)
  linarith only [h]

lemma high_tail_polynomial {B κ P q : ℝ} (hB : 0<B) (hq : 0<q)
    (p : ℕ) (hκ : κ+Real.log 10≤P/20) (hp : 1000*Real.log q≤(p:ℝ)*P) :
    (B^p*Real.exp (-(1/10:ℝ)*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p≤q^(-(50:ℝ)) := by
  apply (high_tail_ratio hB p hκ).trans
  rw [Real.rpow_def_of_pos hq]
  exact Real.exp_le_exp.mpr (by linarith only [hp])

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_UniformTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

theorem eventually_score_slack {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb A k c : ℝ) (hCb : 0≤Cb) (hk : 1≤k) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R b τ : ℝ,Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      b+k*P η σ D R*τ+A ≤ c*L η σ D := by
  have hk0 : 0<k := by linarith
  have he := eventually_hierarchy hη hη' Cb (c/(2*k)) (2*max A 0/c) hCb (by positivity)
  filter_upwards [he] with σ he
  intro D R b τ hr hb hbhi hτ
  have hs := he D R b τ hr hbhi hτ
  have hA : A ≤ c*L η σ D/2 := by
    have hh := (div_le_iff₀ hc).mp hs.1
    linarith [le_max_left A 0]
  have hB : b+k*P η σ D R*τ≤k*(b+P η σ D R*τ) := by nlinarith only [hb,hk]
  have hh := mul_le_mul_of_nonneg_left hs.2.2.2.2.1 hk0.le
  have hx : k*(c/(2*k)*L η σ D)=c*L η σ D/2 := by field_simp
  rw [hx] at hh
  linarith only [hA,hB,hh]

theorem eventually_R_le_L {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R : ℝ,Range η σ D R → R ≤ c*L η σ D := by
  have hb : 0<8*beta η := mul_pos (by norm_num) (beta_pos hη)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (4/c))] with σ hσ hlarge
  intro D R hr
  have hs : 0<σ := by linarith
  obtain ⟨hD,hR,hpow,hL,hLhi,hP,hPhi⟩ := finite_bounds hη hη' hσ hr
  have hR' : R≤4*σ^beta η := hr.rhi.trans (by linarith)
  have h4 : 4 ≤ c*σ^(8*beta η) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    nlinarith only [hh]
  calc
    R ≤ 4*σ^beta η := hR'
    _ ≤ (c*σ^(8*beta η))*σ^beta η := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = c*σ^(9*beta η) := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
    _ ≤ c*L η σ D := mul_le_mul_of_nonneg_left hL hc.le

theorem eventually_score_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ),Range η σ D R → 0≤b →
      b≤Cb*D*σ^(6*beta η) → τ≤σ^(-200*beta η) →
      let ℓ := L η σ D
      let Q := P η σ D R
      let κ := b+8*Q*τ+Real.log 16
      1000000≤ℓ ∧ 100000≤Q ∧ (R:ℝ)≤Q/100000 ∧ 100*ℓ≤Q ∧
      (R:ℝ)*Real.log ℓ≤Q/100 ∧ κ+Real.log 10≤Q/20 ∧
      κ+Real.log 100≤(91/100:ℝ)*ℓ ∧
      (R:ℝ)*Real.exp (-(23/25:ℝ)*ℓ)≤1/10 := by
  have hs := eventually_score_slack hη hη' Cb (Real.log 16+Real.log 100+Real.log 10) 8
    (1/100) hCb (by norm_num) (by norm_num)
  have hh := eventually_hierarchy hη hη' Cb (1/100) 1000000 hCb (by norm_num)
  have hr := eventually_R_le_L hη hη' (c:=1) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hs,hh,hr] with σ hσ hs hh hr
  intro D b τ R hRange hb hbhi hτ
  dsimp only
  have hs := hs D R b τ hRange hb hbhi hτ
  have hh := hh D R b τ hRange hbhi hτ
  have hr : (R:ℝ)≤L η σ D := by simpa using hr D R hRange
  let ℓ := L η σ D
  let Q := P η σ D R
  have hL : 1000000≤ℓ := hh.1
  have hL0 : 0≤ℓ := by linarith only [hL]
  have hR1 : 1≤(R:ℝ) := (finite_bounds hη hη' hσ hRange).2.2.1.trans hRange.rlo
  have hP : ℓ≤Q := by dsimp [Q,P];nlinarith only [hR1,hL0]
  have hRsmall : (R:ℝ)≤Q/100000 := by dsimp [Q,P];nlinarith only [hL,(Nat.cast_nonneg R : (0:ℝ)≤R)]
  have hLP : 100*ℓ≤Q := by nlinarith only [hh.2.2.2.2.2]
  have hlog10 : 0≤Real.log 10 := Real.log_nonneg (by norm_num)
  have hlog100 : 0≤Real.log 100 := Real.log_nonneg (by norm_num)
  have hκP : b+8*Q*τ+Real.log 16+Real.log 10≤Q/20 := by
    change b+8*Q*τ+(Real.log 16+Real.log 100+Real.log 10)≤(1/100:ℝ)*ℓ at hs
    linarith only [hs,hlog100,hP,hL0]
  have hκL : b+8*Q*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*ℓ := by
    linarith only [hs,hlog10,hL0]
  refine ⟨hL,by linarith only [hL,hP],hRsmall,hLP,?_,hκP,hκL,?_⟩
  · simpa only [div_eq_mul_inv,mul_comm (100⁻¹:ℝ),one_mul] using hh.2.2.2.1
  · have he : ℓ≤Real.exp (ℓ/2) := by
      have he := Real.add_one_le_exp (ℓ/4)
      have hp : 0≤ℓ/4+1 := by positivity
      have hh := mul_self_le_mul_self hp he
      rw [←Real.exp_add] at hh
      have hex : ℓ/4+ℓ/4=ℓ/2 := by ring
      rw [hex] at hh
      nlinarith only [hh,sq_nonneg (ℓ/4-1)]
    have he2 : Real.exp (-(21/50:ℝ)*ℓ)≤1/10 := by
      have hx : (10:ℝ)≤Real.exp ((21/50:ℝ)*ℓ) := by
        linarith [Real.add_one_le_exp ((21/50:ℝ)*ℓ)]
      rw [show -(21/50:ℝ)*ℓ=-((21/50:ℝ)*ℓ) by ring,Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10) hx
    calc
      _ ≤ Real.exp (ℓ/2)*Real.exp (-(23/25:ℝ)*ℓ) :=
        mul_le_mul_of_nonneg_right (hr.trans he) (Real.exp_nonneg _)
      _ = Real.exp (-(21/50:ℝ)*ℓ) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := he2

end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_UniformHighTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_local_trunc_scalar_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ D R g : ℝ,Range η σ D R → P η σ D R/20000≤g →
      localTruncConstant*σ*(P η σ D R)^5000*
        Real.exp (P η σ D R/100-4901*g)≤1 := by
  have hab := eventually_power_absorption hη hη' localTruncConstant 5001 (1/10)
    localTruncConstant_pos (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R g hr hg
  have hp := (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  have hP0 : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hp
  have hPσ : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hc : localTruncConstant*σ*(P η σ D R)^5000≤Real.exp (P η σ D R/10) := by
    calc
      _ ≤ localTruncConstant*σ*σ^5000 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hP0 hPσ _) (mul_nonneg localTruncConstant_pos.le (by linarith))
      _ = localTruncConstant*σ^(5001:ℕ) := by rw [show σ^(5001:ℕ)=σ^5000*σ from pow_succ σ 5000]; ac_rfl
      _ ≤ _ := by
        have hh := hab D R hr
        rw [show σ^(5001:ℝ)=σ^(5001:ℕ) from Real.rpow_natCast σ 5001] at hh
        simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using hh
  calc
    _ ≤ Real.exp (P η σ D R/10)*Real.exp (P η σ D R/100-4901*g) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (P η σ D R/10+(P η σ D R/100-4901*g)) := (Real.exp_add ..).symm
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

theorem eventually_high_local_budget_retained {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q m : ℕ) (n D : ℝ) (R : ℕ),
      (q:ℝ)=Real.exp σ → 0<n → (m:ℝ)≤Real.exp (3*σ) →
      Range η σ D R → (q:ℝ)^2*Real.exp (P η σ D R/20000)≤n →
      ((q:ℝ)/n*((q:ℝ)+1)≤2) ∧
      (208*2^198:ℝ)≤Real.exp (2*(P η σ D R/100)) ∧
      (pencilAlphabet q 3:ℝ)*(P η σ D R)^5000*
        (((q:ℝ)/n*((q:ℝ)+1))^4900*
          (2^200*((Nat.clog 2 m:ℝ)+1)*
            ((q:ℝ)^4/n^2*Real.exp (P η σ D R/100))))≤geometryScale q n := by
  have ht := eventually_local_trunc_scalar_retained hη hη'
  have hs := eventually_hierarchy hη hη' 0 1
    (max 10000 (50*Real.log (208*2^(198:ℕ)))) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht,hs] with σ hσ ht hs
  intro q m n D R hq hn hm hr hnlo
  obtain ⟨hD,hR,hpow,hLlo,hLhi,hPlo,hPhi⟩ := finite_bounds hη hη' hσ hr
  have hR1 : 1≤(R:ℝ) := hpow.trans hr.rlo
  have hL : max 10000 (50*Real.log (208*2^(198:ℕ)))≤L η σ D :=
    (hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)).1
  have hL0 : 0≤L η σ D := by linarith [le_max_left (10000:ℝ) (50*Real.log (208*2^(198:ℕ)))]
  have hLP : L η σ D≤P η σ D R := by unfold P;nlinarith
  have hP0 : 0≤P η σ D R := hL0.trans hLP
  let g := Real.log n-2*σ
  have hnexp : n=Real.exp (2*σ+g) := by
    rw [show 2*σ+g=Real.log n by dsimp [g];ring,Real.exp_log hn]
  have hq2 : (q:ℝ)^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul];norm_num
  have hg : P η σ D R/20000≤g := by
    rw [hq2,hnexp,←Real.exp_add,Real.exp_le_exp] at hnlo
    linarith
  have hg0 : 0≤g := (by positivity : 0≤P η σ D R/20000).trans hg
  have hq1 : 1≤(q:ℝ) := by rw [hq];exact Real.one_le_exp_iff.mpr (by linarith)
  have heq : (q:ℝ)^2/n=Real.exp (-g) := by
    rw [hq2,hnexp,←Real.exp_sub]
    congr 1
    ring
  have hM : 0≤(q:ℝ)/n*((q:ℝ)+1) := by positivity
  have hMhi : (q:ℝ)/n*((q:ℝ)+1)≤2*Real.exp (-g) := by
    rw [←heq]
    calc
      _ = ((q:ℝ)*((q:ℝ)+1))/n := by ring
      _ ≤ (2*(q:ℝ)^2)/n := div_le_div_of_nonneg_right (by nlinarith [hq1]) hn.le
      _ = _ := by ring
  have hMmax : (q:ℝ)/n*((q:ℝ)+1)≤2 := by
    exact hMhi.trans (by nlinarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg0)])
  refine ⟨hMmax,?_,?_⟩
  · have hc : (0:ℝ)<208*2^(198:ℕ) := mul_pos (by norm_num) (pow_pos (by norm_num) _)
    apply (Real.log_le_iff_le_exp hc).mp
    have hh := le_max_right (10000:ℝ) (50*Real.log (208*2^(198:ℕ)))
    have hlog : 50*Real.log (208*2^(198:ℕ):ℝ)≤P η σ D R := hh.trans (hL.trans hLP)
    calc
      Real.log (208*2^(198:ℕ):ℝ) = (50*Real.log (208*2^(198:ℕ):ℝ))/50 := by ring
      _ ≤ P η σ D R/50 := div_le_div_of_nonneg_right hlog (by norm_num)
      _ = _ := by ring
  · exact (high_local_radial_numeric hσ hq hnexp hP0 hM
      (hMhi.trans (by linarith [Real.exp_nonneg (-g)])) hm).trans
      (by
        have hB : 0≤geometryScale q n := by unfold geometryScale;positivity
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left (ht D R g hr hg) hB))

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_high_original_tail_retained_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (5*σ/2) →
      (Nat.card K:ℝ)^2*Real.exp (P η σ D R/20000)≤(S.card:ℝ) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      ∀ (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      (∀i∈boundedOverlapDyads x (outsideAt x S (C a∪C b)) (pointStrength S) 2,
        x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
          (((pointStrength S:ℝ)*2^i)/2) Lines Q
          ((Nat.card K:ℝ)^4/S.card^2*Real.exp (P η σ D R/100)/
            (((pointStrength S:ℝ)*2^i)/2)^100)) →
      ((∑z : WeightedPrograms.DistinctPairs F,WeightedPrograms.strength (pencilLines x F)
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z^200)≤
        dyadFactor (outsideAt x S (C a∪C b)).card (P η σ D R/100)*
          (geometryScale (Nat.card K) S.card)^2) →
      x∉GlobalRadial.badCenters S (fun _ => C a∪C b) (pointStrength S)
        ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 →
      geometryScale (Nat.card K) S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ))+
      ∫ω,1-HighMoment.allTrunc R 5000 ω
        ∂batchMeasure (fun i : Fin R×RadialLine x => L₀*
          radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2) := by
  have hh := eventually_high_geometric_budget hη hη'
  have hl := eventually_high_local_budget_retained hη hη'
  have ho := eventually_moment_orders hη hη'
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  filter_upwards [eventually_ge_atTop (100:ℝ),hh,hl,ho,hm] with σ hσ hh hl ho hm
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hShigh hn hf hF hx Lines Q hLines hxQ hgood hPow hstrong ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hcard : ((outsideAt x S (C a∪C b)).card:ℝ)≤Real.exp (3*σ) := by
    have hsub : (outsideAt x S (C a∪C b)).card≤S.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        have hy' : y.val∈S\(C a∪C b) := by simpa [outsideAt] using hy
        exact (Finset.mem_sdiff.mp hy').1
      · intro y hy z hz he
        exact Subtype.ext he
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr hsub
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := by
        exact mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hbudget := hh (Nat.card K) (outsideAt x S (C a∪C b)).card S.card D R
    hq hsn hSn hcard hr
  have hlocal := hl (Nat.card K) (outsideAt x S (C a∪C b)).card S.card D R
    hq hsn hcard hr hShigh
  obtain ⟨heven,hp,hplo,hphi,hps,hKR,hhpos,hhsize,herr⟩ := ho D R hr
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hP0 : 0<P η σ D R := lt_of_lt_of_le (by norm_num) hmargin.2.1
  have hpP : 1000*Real.log (Nat.card K)≤(momentOrder σ (P η σ D R):ℝ)*((L₀:ℝ)*R) := by
    rw [hq,Real.log_exp,hPL]
    have ht := (div_le_iff₀ hP0).mp hplo
    linarith only [ht,hσ]
  have hB : 0<geometryScale (Nat.card K) S.card := by
    unfold geometryScale
    have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    positivity
  have ht0 : 0<geometryScale (Nat.card K) S.card*
      Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 := by positivity
  have hb0 : Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L₀.coe_nonneg) (by linarith only [hf])
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add,hq,←Real.exp_nat_mul];congr 1;norm_num;ring
  have hmoment := actual_high_radial_moment x hdim S C hS a b c ha hb hc F hF hf hn L₀
    (by simpa only [hL] using hbudget.1) R (momentOrder σ (P η σ D R)) (residualOrder σ)
    hp hKR hhpos hhsize herr hx (Real.exp (σ/5))
    (Real.one_le_exp_iff.mpr (by linarith only [hσ])) hcap
    (by simpa only [hPL] using hlocal.2.1)
    (by simpa only [coe_pointStrength] using hlocal.1) Lines hLines Q hxQ
    (by simpa only [hPL] using hgood) (by simpa only [hPL] using hPow)
    (by simpa only [coe_pointStrength,mul_comm (R:ℝ) (L₀:ℝ),hPL] using hlocal.2.2)
    (by simpa only [hL,pencilHighBudget,ParameterHierarchy.P] using hbudget.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.2.1)
    (by simpa only [hPL] using hbudget.2.2.2.2.2) hstrong
    (by simpa only [hPL] using hbudget.2.2.1)
  have hprob := unsampled_score_tail x S (C a∪C b) L₀ (pointStrength S) F
    (fun H hH => (hF H hH).1) hb0 heven ht0 hmoment
  have hpoly := ScoreScalars.high_tail_polynomial hB
    (by exact_mod_cast (Nat.card_pos (α:=K)) : (0:ℝ)<Nat.card K)
    (momentOrder σ (P η σ D R))
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) hpP
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L₀*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans (add_le_add hpoly (le_refl _)))
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_high_original_tail_retained_oai
