-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_three_score_integrals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:40:54.581897+00:00
-- url     : https://prove2.me/submissions/3945b03b-a766-4487-808a-f8127f054b3a

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_literal_plane_exceptions
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_three_ambient_tail_cases
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_validation_original_tail

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

lemma sum_trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    ∑ l ∈ inFlat W, (trainingOnLine X l).card =
      (X.filter (fun y => y.val.submodule ≤ W)).card := by
  classical
  simp_rw [trainingOnLine_eq_fiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter X (inFlat W)
    (fun y => through x y.val y.property)]
  congr 1
  ext y
  simp [inFlat, through_le_iff, hx]

omit [FiniteDimensional K V] in
lemma inFlat_inf (W U : Submodule K V) :
    (inFlat (x := x) W) ∩ inFlat U = inFlat (W ⊓ U) := by
  classical
  ext l
  simp [inFlat]

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]

lemma incident_eval (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident b (projectiveEquiv (Module.evalEquiv K V) a) ↔ Incident a b := by
  change Incident b (Projectivization.map (Module.evalEquiv K V).toLinearMap (Module.evalEquiv K V).injective a) ↔ _
  conv_lhs => rw [←a.mk_rep,Projectivization.map_mk,incident_mk_right]
  rw [incident_iff]
  rfl

variable [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [Finite K] [Fintype (ℙ K V)] in
lemma weightOnPencil_eq (w : ℙ K (Module.Dual K V) → ℝ) (a : ℙ K V) :
    weightOnPencil w a = weightOnHyperplane w (projectiveEquiv (Module.evalEquiv K V) a) := by
  unfold weightOnPencil weightOnHyperplane
  apply Finset.sum_congr rfl
  intro b _
  simp only [incidenceEntry,incident_eval]

theorem pencil_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (w : ℙ K (Module.Dual K V) → ℝ) :
    ∑ a, (weightOnPencil w a -
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b))^2 ≤
      (Nat.card K:ℝ)^(d-1)*∑ b,w b^2 := by
  let : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
  let := Fintype.ofFinite (ℙ K (Module.Dual K (Module.Dual K V)))
  have hd' : finrank K (Module.Dual K V) = d+1 := by simpa only [Subspace.dual_finrank_eq] using hdim
  have h := incidence_variance hd' hd w
  rw [←(projectiveEquiv (Module.evalEquiv K V)).sum_comp] at h
  simpa only [←weightOnPencil_eq] using h

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_LargeValueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PencilRegularity
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

lemma large_value_count {I : Type*} [Fintype I] (f : I → ℝ) (μ h : ℝ)
    (hh : 0 ≤ h) (hμ : μ ≤ h/2) :
    ((Finset.univ.filter fun i => h ≤ f i).card:ℝ) * h^2 ≤
      4*∑ i,(f i-μ)^2 := by
  let E := Finset.univ.filter fun i => h ≤ f i
  have hb (i : I) (hi : i ∈ E) : h^2 ≤ 4*(f i-μ)^2 := by
    have hf := (Finset.mem_filter.mp hi).2
    have hs : h/2 ≤ f i-μ := by linarith
    nlinarith [sq_nonneg (f i-μ-h/2)]
  have hs := Finset.sum_le_sum (s:=E) hb
  simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    (fun i _ _ => sq_nonneg _)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem clipped_pencil_count {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (w : ℙ K (Module.Dual K V) → ℝ) (hw0 : ∀ b,0 ≤ w b) (hw1 : ∀ b,w b ≤ 1)
    (h : ℝ) (hh : 0 ≤ h)
    (hmean : ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b) ≤ h/2) :
    ((Finset.univ.filter fun a => h ≤ weightOnPencil w a).card:ℝ)*h^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(∑ b,w b) := by
  have hc := large_value_count (weightOnPencil w) _ h hh hmean
  have hv := pencil_variance hdim hd w
  have hn : (∑ b,w b^2) ≤ ∑ b,w b := Finset.sum_le_sum fun b _ => by
    nlinarith [mul_nonneg (hw0 b) (sub_nonneg.mpr (hw1 b))]
  calc
    _ ≤ 4*∑ a,(weightOnPencil w a -
        ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b))^2 := hc
    _ ≤ 4*((Nat.card K:ℝ)^(d-1)*∑ b,w b^2) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ ≤ 4*((Nat.card K:ℝ)^(d-1)*∑ b,w b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (by positivity)) (by norm_num)
    _ = _ := by ring

theorem family_irregular_count {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    {J : Type*} [Fintype J] (w : J → ℙ K (Module.Dual K V) → ℝ)
    (hw0 : ∀ j b,0 ≤ w j b) (hw1 : ∀ j b,w j b ≤ 1) (h : ℝ) (hh : 0 ≤ h)
    (hmean : ∀ j, ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w j b) ≤ h/2) :
    ((Finset.univ.filter fun a => ∃ j,h ≤ weightOnPencil (w j) a).card:ℝ)*h^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(∑ j,∑ b,w j b) := by
  let E : J → Finset (ℙ K V) := fun j => Finset.univ.filter fun a => h ≤ weightOnPencil (w j) a
  have heq : (Finset.univ.filter fun a => ∃ j,h ≤ weightOnPencil (w j) a) =
      Finset.univ.biUnion E := by ext a; simp [E]
  rw [heq]
  have hc : ((Finset.univ.biUnion E).card:ℝ) ≤ ∑ j,((E j).card:ℝ) := by
    exact_mod_cast Finset.card_biUnion_le (s:=Finset.univ) (t:=E)
  calc
    _ ≤ (∑ j,((E j).card:ℝ))*h^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg h)
    _ = ∑ j,((E j).card:ℝ)*h^2 := Finset.sum_mul ..
    _ ≤ ∑ j,4*(Nat.card K:ℝ)^(d-1)*(∑ b,w j b) := Finset.sum_le_sum fun j _ =>
      clipped_pencil_count hdim hd (w j) (hw0 j) (hw1 j) h hh (hmean j)
    _ = _ := (Finset.mul_sum ..).symm

end SharpRamseyFive.PencilRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ExceptionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma ker_dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) :
    LinearMap.ker (dualOfHyperplane hdim A hA).rep = A := by
  let b := dualOfHyperplane hdim A hA
  have he : b.submodule = A.dualAnnihilator := Projectivization.submodule_mk'' _ _
  have hmem : b.rep ∈ A.dualAnnihilator := by
    rw [← he, b.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hle : A ≤ LinearMap.ker b.rep := by
    intro a ha
    exact ((Submodule.mem_dualAnnihilator b.rep).mp hmem) a ha
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA]; omega)).symm

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardFilterContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

end SharpRamseyFive.RichPlaneGeometry

namespace SharpRamseyFive.HyperplaneOverlap
open Module ProjectiveIncidence RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma hyperplane_intersection_rank {d : ℕ} (hdim : finrank K V = d+1)
    (A B : Submodule K V) (hA : finrank K A = d) (hB : finrank K B = d) (hne : A ≠ B) :
    finrank K (A ⊓ B : Submodule K V) = d-1 := by
  have hn : ¬A ≤ B := fun h => hne (Submodule.eq_of_le_of_finrank_eq h (hA.trans hB.symm))
  have hlt := finrank_inf_lt_of_not_le A B hn
  have hs := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle := Submodule.finrank_le (A ⊔ B : Submodule K V)
  rw [hA] at hlt
  rw [hA,hB] at hs
  rw [hdim] at hle
  omega

lemma card_hyperplanes_containing [Finite K] {d : ℕ} (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) (W : Submodule K V) :
    (F.filter fun A => W ≤ A).card ≤
      ∑ i ∈ Finset.range (d+1-finrank K W), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let G := F.filter fun A => W ≤ A
  let f (A : G) : {b : ℙ K (Module.Dual K V) // b.submodule ≤ W.dualAnnihilator} :=
    ⟨dualOfHyperplane hdim A.val (hF _ (Finset.mem_filter.mp A.property).1), by
      rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,Submodule.mem_dualAnnihilator]
      intro w hw
      have hk := (Finset.mem_filter.mp A.property).2 hw
      rw [← ker_dualOfHyperplane hdim A.val (hF _ (Finset.mem_filter.mp A.property).1)] at hk
      exact hk⟩
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hv := congrArg (fun b : {b : ℙ K (Module.Dual K V) // b.submodule ≤ W.dualAnnihilator} =>
      LinearMap.ker b.val.rep) he
    simpa only [f,ker_dualOfHyperplane] using hv
  have hc := Fintype.card_le_of_injective f hf
  have he := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hr : finrank K W.dualAnnihilator = d+1-finrank K W := by omega
  rw [Fintype.card_coe,← Nat.card_eq_fintype_card,card_subspacePoints,hr] at hc
  exact hc

lemma pair_count_by_contained_witness {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V × Submodule K V))
    (hE : E ⊆ F ×ˢ F) (hEL : ∀ p ∈ E, ∃ W ∈ L, W ≤ p.1 ⊓ p.2) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
  let C (W : Submodule K V) := F.filter fun H => W ≤ H
  have hsub : E ⊆ L.biUnion (fun W => C W ×ˢ C W) := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hE hp)
    obtain ⟨W,hW,hWp⟩ := hEL p hp
    exact Finset.mem_biUnion.mpr ⟨W,hW,Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,hWp.trans inf_le_left⟩,
       Finset.mem_filter.mpr ⟨hb,hWp.trans inf_le_right⟩⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (C W ×ˢ C W).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i)^2 := by
    have hc := card_hyperplanes_containing hdim F hF W
    rw [hL W hW] at hc
    simpa only [Finset.card_product,pow_two] using Nat.pow_le_pow_left hc 2
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

end SharpRamseyFive.HyperplaneOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PairPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ActualOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

theorem dominant_pair_count [Fintype (RadialLine x)] {d : ℕ}
    (hdim : finrank K V = d+1) (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (E : Finset (Submodule K V × Submodule K V)) (hE : E ⊆ F ×ˢ F) (M : ℕ)
    (hdom : ∀ p ∈ E, ∃ l : RadialLine x, l.val ≤ p.1 ⊓ p.2 ∧
      M ≤ (RadialLine.trainingOnLine X l).card) :
    E.card ≤ (richRadials x X ⊤ M).card * (∑ i ∈ Finset.range (d-1), Nat.card K^i)^2 := by
  let R := richRadials x X ⊤ M
  let L := R.image Subtype.val
  have hcL : L.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 2 := by
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hW
    exact l.property.1
  have hN := pair_count_by_contained_witness hdim F hF L 2 hL E hE (by
    intro p hp
    obtain ⟨l,hl,hM⟩ := hdom p hp
    refine ⟨l.val,Finset.mem_image.mpr ⟨l,?_,rfl⟩,hl⟩
    refine Finset.mem_filter.mpr ⟨?_,hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := RadialLine x) l, le_top⟩)
  rw [hcL] at hN
  have he : d+1-2 = d-1 := by omega
  simpa only [he] using hN

omit [Finite K] in

theorem intersection_radial_three (hdim : finrank K V = 4)
    (A B : Submodule K V) (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B) (hne : A ≠ B)
    (X : Finset {y : ℙ K V // x ≠ y}) :
    ∃ l : RadialLine x, l.val = A ⊓ B ∧
      RadialLine.trainingOnLine X l = pairPoints x X A B := by
  let l : RadialLine x := ⟨A ⊓ B,
    hyperplane_intersection_rank (d := 3) hdim A B hA hB hne, le_inf hxA hxB⟩
  exact ⟨l,rfl,rfl⟩

end SharpRamseyFive.ActualOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_CellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.CellVariance
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

lemma sum_shift_square {I : Type*} [Fintype I] (f : I → ℝ) (a b : ℝ) :
    (∑ i,(f i-b)^2) ≤ 2*(∑ i,(f i-a)^2)+2*Fintype.card I*(a-b)^2 := by
  calc
    _ ≤ ∑ i,(2*(f i-a)^2+2*(a-b)^2) := Finset.sum_le_sum fun i _ => by
      nlinarith [sq_nonneg ((f i-a)-(a-b))]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Module.Dual K V))] in
lemma weight_indicator (C : Finset (ℙ K V)) (δ : ℝ) (b : ℙ K (Module.Dual K V)) :
    weightOnHyperplane (fun a => if a ∈ C then δ else 0) b = cellMass C δ b := by
  simp only [weightOnHyperplane,mul_ite,mul_zero,Finset.sum_ite_mem,Finset.univ_inter]
  rw [← Finset.sum_mul]
  have he : (∑ a ∈ C,incidenceEntry a b) = ((C.filter fun a => Incident a b).card:ℝ) := by
    exact Finset.sum_boole _ _
  rw [he,cellMass,mul_comm]

theorem cell_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (C : Finset (ℙ K V)) (δ : ℝ) :
    ∑ b,(cellMass C δ b - δ*C.card/(Nat.card K:ℝ))^2 ≤
      4*δ^2*(Nat.card K:ℝ)^(d-1)*C.card := by
  let q : ℝ := Nat.card K
  let N : ℝ := Q (Nat.card K) d
  let c : ℝ := C.card
  let p : ℝ := (Q (Nat.card K) (d-1):ℝ)/N
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Q_pos (Nat.card K) d
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c ≤ N := by
    dsimp [c,N]
    exact_mod_cast (C.card_le_univ.trans_eq (card_points hdim))
  have hp : p-1/q = -(1/(q*N)) := by
    dsimp [p]
    have hr : N = q*(Q (Nat.card K) (d-1):ℝ)+1 := by
      dsimp [N,q]
      exact_mod_cast Q_recurrence (q:=Nat.card K) hd
    field_simp
    nlinarith
  let w : ℙ K V → ℝ := fun a => if a ∈ C then δ else 0
  have hsum : (∑ a,w a) = δ*c := by simp [w,c,Finset.sum_ite_mem,mul_comm]
  have hsq : (∑ a,w a^2) = δ^2*c := by simp [w,c,Finset.sum_ite_mem,mul_comm]
  have hv := incidence_variance hdim hd w
  rw [hsum,hsq] at hv
  simp_rw [show ∀ b,weightOnHyperplane w b = cellMass C δ b from fun b => weight_indicator C δ b] at hv
  change (∑ b,(cellMass C δ b-p*(δ*c))^2) ≤ q^(d-1)*(δ^2*c) at hv
  have he : p*(δ*c)-δ*c/q = -(δ*c/(q*N)) := by
    calc
      _ = (p-1/q)*(δ*c) := by ring
      _ = _ := by rw [hp]; ring
  have hcor : N*(p*(δ*c)-δ*c/q)^2 ≤ δ^2*c := by
    rw [he]
    have heq : N*(-(δ*c/(q*N)))^2 = δ^2*c^2/(q^2*N) := by
      have hq0 : q ≠ 0 := by linarith
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < q^2*N)).mpr
    have hq2 : 1 ≤ q^2 := by nlinarith
    have hbound : c ≤ q^2*N := hcN.trans (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg δ) hc)
    nlinarith
  have hpow : 1 ≤ q^(d-1) := one_le_pow₀ hq
  have hs := sum_shift_square (cellMass C δ) (p*(δ*c)) (δ*c/q)
  rw [card_hyperplanes hdim] at hs
  change (∑ b,(cellMass C δ b-δ*c/q)^2) ≤ 2*(∑ b,(cellMass C δ b-p*(δ*c))^2)+
    2*N*(p*(δ*c)-δ*c/q)^2 at hs
  change (∑ b,(cellMass C δ b-δ*c/q)^2) ≤ 4*δ^2*q^(d-1)*c
  have hh := mul_le_mul_of_nonneg_right hpow (mul_nonneg (sq_nonneg δ) hc)
  nlinarith

end SharpRamseyFive.CellVariance

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma scale_nonneg (d : ℕ) (n : ℝ) (hn : 0≤n) : 0≤ scale (K:=K) d n := by
  unfold scale
  positivity

lemma cell_variance_scale {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (C : Finset (ℙ K V)) {n : ℝ} (hn : 0<n) :
    (∑ H,(cellMass C ((Nat.card K:ℝ)/n) H-(C.card:ℝ)/n)^2)≤
      4*(Nat.card K:ℝ)*scale (K:=K) d n*(C.card/n) := by
  have hq : (Nat.card K:ℝ)≠0 := by exact_mod_cast (Nat.card_pos (α:=K)).ne'
  have hv := cell_variance hdim hd C ((Nat.card K:ℝ)/n)
  have he (a : ℝ) : a^(d-1)*a=a^d := by rw [←pow_succ]; congr 1; omega
  have hc : ((Nat.card K:ℝ)/n)*C.card/(Nat.card K:ℝ)=(C.card:ℝ)/n := by field_simp
  rw [hc] at hv
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  unfold scale
  rw [←he (Nat.card K:ℝ)]
  ring

lemma total_deviation_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ j : Option J,∑ H,(deviation S C j H)^2)≤
      16*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hsum : (∑ j : Option J,((familyCell S C j).card:ℝ)/(S.card:ℝ))≤4 := by
    rw [Fintype.sum_option]
    simp only [familyCell,div_self hn.ne',←Finset.sum_div]
    have hC' : (∑ j,((C j).card:ℝ))≤3*(S.card:ℝ) := by exact_mod_cast hC
    have hh := (div_le_iff₀ hn).mpr hC'
    linarith
  calc
    _ ≤ ∑ j : Option J,4*(Nat.card K:ℝ)*scale (K:=K) d S.card*
        ((familyCell S C j).card/(S.card:ℝ)) :=
      Finset.sum_le_sum fun j _ => cell_variance_scale hdim hd _ hn
    _ = 4*(Nat.card K:ℝ)*scale (K:=K) d S.card*
        (∑ j : Option J,((familyCell S C j).card:ℝ)/(S.card:ℝ)) :=
      (Finset.mul_sum ..).symm
    _ ≤ 4*(Nat.card K:ℝ)*scale (K:=K) d S.card*4 :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) (scale_nonneg _ _ hn.le))
    _ = _ := by ring

lemma exceptional_card_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    ((exceptional S C).card:ℝ)≤40000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hsq (H : ℙ K (Dual K V)) (hH : H∈exceptional S C) :
      (1:ℝ)≤2500*∑ j : Option J,(deviation S C j H)^2 := by
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hH).2
    have ht : (1/50:ℝ)≤threshold j := by cases j <;> norm_num [threshold]
    have h := ht.trans hj.le
    have he := sq_abs (deviation S C j H)
    have ha := abs_nonneg (deviation S C j H)
    have hu : (deviation S C j H)^2≤∑ k : Option J,(deviation S C k H)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (deviation S C k H)) (Finset.mem_univ j)
    nlinarith
  have hn : 0≤ scale (K:=K) d S.card := scale_nonneg _ _ (Nat.cast_nonneg _)
  calc
    _ = ∑ H∈exceptional S C,(1:ℝ) := by simp
    _ ≤ ∑ H∈exceptional S C,2500*∑ j : Option J,(deviation S C j H)^2 :=
      Finset.sum_le_sum hsq
    _ = 2500*∑ H∈exceptional S C,∑ j : Option J,(deviation S C j H)^2 :=
      (Finset.mul_sum ..).symm
    _ ≤ 2500*∑ H,∑ j : Option J,(deviation S C j H)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by norm_num)
    _ = 2500*∑ j : Option J,∑ H,(deviation S C j H)^2 := by rw [Finset.sum_comm]
    _ ≤ 2500*(16*(Nat.card K:ℝ)*scale (K:=K) d S.card) :=
      mul_le_mul_of_nonneg_left (total_deviation_bound hdim hd S C hS hC) (by norm_num)
    _ = _ := by ring

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma clippedWeight_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (j : Option (Option J)) (H : ℙ K (Dual K V)) :
    0 ≤ clippedWeight S C j H ∧ clippedWeight S C j H≤1 := by
  cases j with
  | none => simp only [clippedWeight]; split <;> norm_num
  | some j => exact ⟨le_min (by norm_num) (sq_nonneg _),min_le_left _ _⟩

lemma clippedWeight_sum_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ j : Option (Option J),∑ H,clippedWeight S C j H)≤
      50000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  rw [Fintype.sum_option]
  have hi : (∑ H,clippedWeight S C none H)=((exceptional S C).card:ℝ) := by
    simp [clippedWeight]
  rw [hi]
  have hc : (∑ j : Option J,∑ H,clippedWeight S C (some j) H)≤
      ∑ j : Option J,∑ H,(deviation S C j H)^2 :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun H _ => min_le_right _ _
  have he := exceptional_card_bound hdim hd S C hS hC
  have hv := total_deviation_bound hdim hd S C hS hC
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card K) : (0:ℝ)≤Nat.card K) hB]

lemma mean_ratio_le {d : ℕ} (hd : 1≤d) :
    ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)≤1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  have he : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 :=
    by exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  nlinarith

theorem irregular_card_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card)
    {ξ : ℝ} (hξ : 100000≤Real.exp ξ) :
    ((irregular (d:=d) S C ξ).card:ℝ)≤200000*(S.card:ℝ)*Real.exp (-2*ξ) := by
  let B : ℝ := scale (K:=K) d S.card
  let w := clippedWeight S C
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hB : 0<B := by dsimp [B,scale]; positivity
  have hw : ∀ j H,0≤w j H := fun j H => (clippedWeight_bounds S C j H).1
  have htotal := clippedWeight_sum_bound hdim hd S C hS hC
  have hmean (j : Option (Option J)) :
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ H,w j H) ≤ B*Real.exp ξ/2 := by
    have hs : (∑ H,w j H)≤∑ i : Option (Option J),∑ H,w i H :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun H _ => hw i H) (Finset.mem_univ j)
    have hc : ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)≥0 := by positivity
    calc
      _ ≤ (1/(Nat.card K:ℝ))*(∑ H,w j H) :=
        mul_le_mul_of_nonneg_right (mean_ratio_le (K:=K) hd) (Finset.sum_nonneg fun H _ => hw j H)
      _ ≤ (1/(Nat.card K:ℝ))*(50000*(Nat.card K:ℝ)*B) :=
        mul_le_mul_of_nonneg_left (hs.trans htotal) (by positivity)
      _ = 50000*B := by field_simp
      _ ≤ _ := by nlinarith
  have hr := family_irregular_count hdim hd w hw
    (fun j H => (clippedWeight_bounds S C j H).2) (B*Real.exp ξ) (by positivity) hmean
  have hcard : ((irregular (d:=d) S C ξ).card:ℝ)≤
      ((Finset.univ.filter fun x : ℙ K V => ∃ j : Option (Option J),
        B*Real.exp ξ≤weightOnPencil (w j) x).card:ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj.le⟩
  have hp : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  have he : (Nat.card K:ℝ)^d=B*S.card := by dsimp [B,scale]; field_simp
  have hb : ((irregular (d:=d) S C ξ).card:ℝ)*(B*Real.exp ξ)^2≤
      200000*(S.card:ℝ)*B^2 := by
    calc
      _ ≤ 4*(Nat.card K:ℝ)^(d-1)*(∑ j,∑ H,w j H) :=
        (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)).trans hr
      _ ≤ 4*(Nat.card K:ℝ)^(d-1)*(50000*(Nat.card K:ℝ)*B) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by rw [show 4*(Nat.card K:ℝ)^(d-1)*(50000*(Nat.card K:ℝ)*B)=
        200000*((Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ))*B by ring,hp,he]; ring
  have hb' : ((irregular (d:=d) S C ξ).card:ℝ)*(Real.exp ξ)^2≤200000*(S.card:ℝ) := by
    rw [mul_pow] at hb
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hB)).mp
    nlinarith only [hb]
  have hb'' := (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos ξ))).mpr hb'
  have heq : 200000*(S.card:ℝ)*Real.exp (-2*ξ)=
      200000*(S.card:ℝ)/(Real.exp ξ)^2 := by
    rw [←Real.exp_nat_mul,show -2*ξ=-(2*ξ) by ring,Real.exp_neg]
    norm_num
    ring
  rw [heq]
  exact hb''

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

lemma dyadic_cover (δ x : ℝ) (hδ : 0 ≤ δ) (hx : δ ≤ x) (N : ℕ)
    (hN : x ≤ δ * 2 ^ N) :
    ∃ i ∈ Finset.range (N + 1), δ * 2 ^ i ≤ x ∧ x ≤ 2 * (δ * 2 ^ i) := by
  induction N with
  | zero =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simpa using hx
    · simp only [pow_zero, mul_one] at hN ⊢
      linarith
  | succ N ih =>
    by_cases hh : x ≤ δ * 2 ^ N
    · obtain ⟨i, hi, hix, hxi⟩ := ih hh
      exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), hix, hxi⟩
    · refine ⟨N, Finset.mem_range.mpr (by omega), le_of_lt (lt_of_not_ge hh), ?_⟩
      rw [pow_succ] at hN
      nlinarith

end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators
open SharpRamseyFive.DyadicMoments

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma strength_nonneg (a : D → ℝ≥0) (p : DistinctPairs H) :
    0 ≤ strength lines a p := by unfold strength; positivity

end SharpRamseyFive.WeightedPrograms

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_inFlat (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    PoissonScore.mass (radialWeight x X δ) (RadialLine.inFlat W) =
      (δ:ℝ) * (X.filter fun y => y.val.submodule ≤ W).card := by
  unfold PoissonScore.mass radialWeight
  simp only [NNReal.coe_mul, NNReal.coe_natCast, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [RadialLine.sum_trainingOnLine X W hx]

lemma mass_pencil (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val).card :=
  mass_inFlat x X δ _ (hF H.val H.property)

lemma mass_overlap (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
  unfold pencilLines
  rw [RadialLine.inFlat_inf, mass_inFlat x X δ _ (le_inf (hF H.val H.property)
    (hF H'.val H'.property))]
  simp only [Incident, le_inf_iff]
  rfl

lemma overlap_pos_lower (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F)
    (h : 0 < PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) :
    (δ:ℝ) ≤ PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') := by
  rw [mass_overlap x X δ F hF] at h ⊢
  have hc : 0 < (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    by_contra hn
    have := Nat.eq_zero_of_not_pos hn
    simp [this] at h
  have hcast : (1:ℝ) ≤ (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    exact_mod_cast hc
  exact (mul_one (δ:ℝ)).symm.trans_le (mul_le_mul_of_nonneg_left hcast δ.coe_nonneg)

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma submodule_eq_ker_annihilator (b : ℙ K (Module.Dual K V)) :
    b.submodule = (LinearMap.ker b.rep).dualAnnihilator := by
  have hle : b.submodule ≤ (LinearMap.ker b.rep).dualAnnihilator := by
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,Submodule.mem_dualAnnihilator]
    intro v hv
    exact hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker b.rep)
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  rw [Projectivization.finrank_submodule]
  omega

lemma kernel_injective : Function.Injective (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) := by
  intro b c h
  apply Projectivization.submodule_injective
  simp only [submodule_eq_ker_annihilator,h]

variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_pairPoints (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ)*(ActualOverlap.pairPoints x X (LinearMap.ker H.val.rep)
        (LinearMap.ker H'.val.rep)).card := by
  rw [mass_overlap x X δ F hF]
  simp only [ActualOverlap.pairPoints, NondominantOverlap.onPlane, Incident, le_inf_iff]
  rfl

lemma distinctPairs_ext {H : Type*} {p q : WeightedPrograms.DistinctPairs H}
    (h₁ : p.1=q.1) (h₂ : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨p,p',hp⟩
  rcases q with ⟨q,q',hq⟩
  cases h₁
  cases h₂
  rfl

lemma pair_strength_count_le (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (a : ℝ) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card ≤
    (WeightedOverlap.pairs x X (F.image fun b => LinearMap.ker b.rep) δ a).card := by
  let E := Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a ≤ WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)
  let G := WeightedOverlap.pairs x X (F.image fun b => LinearMap.ker b.rep) δ a
  let f (p : E) : G := ⟨(LinearMap.ker p.val.1.val.rep,LinearMap.ker p.val.2.val.val.rep),by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,p.val.1.property,rfl⟩,
      Finset.mem_image.mpr ⟨_,p.val.2.val.property,rfl⟩⟩,?_,?_⟩
    · intro h
      exact p.val.2.property (Subtype.ext (kernel_injective h).symm)
    · have hp := (Finset.mem_filter.mp p.property).2
      change a ≤ PoissonScore.mass (radialWeight x X δ)
        (pencilLines x F p.val.1 ∩ pencilLines x F p.val.2.val) at hp
      rwa [mass_pairPoints x X δ F hF] at hp⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply distinctPairs_ext
    · apply Subtype.ext
      apply kernel_injective
      exact congrArg (fun z : G => z.val.1) he
    · apply Subtype.ext
      apply kernel_injective
      exact congrArg (fun z : G => z.val.2) he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LocalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_filter_card (S O : Finset (ℙ K V)) (A : Submodule K V) :
    ((outsideAt x S O).filter fun y => y.val.submodule ≤ A).card =
      ((S \ (O ∪ {x})).filter fun y => y.submodule ≤ A).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    have hm : y.val ∈ S \ O := Finset.mem_subtype.mp hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton]
    exact ⟨⟨(Finset.mem_sdiff.mp hm).1,not_or.mpr
      ⟨(Finset.mem_sdiff.mp hm).2,Ne.symm y.property⟩⟩,hyA⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
    have hn : x ≠ y := by
      intro he
      exact hyO (Finset.mem_union_right _ (Finset.mem_singleton.mpr he.symm))
    refine ⟨⟨y,hn⟩,Finset.mem_filter.mpr ⟨?_,hyA⟩,rfl⟩
    exact Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr
      ⟨hyS,fun h => hyO (Finset.mem_union_left _ h)⟩)

lemma richRadials_le_localLines (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (hδ : 0<δ) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) :
    (ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/δ⌉₊).card ≤
      (localLines S O δ a L x).card := by
  let E := ActualOverlap.richRadials x (outsideAt x S (O x)) ⊤ ⌈a/δ⌉₊
  let G := localLines S O δ a L x
  let f (l : E) : G := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hL l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      have hr' : a/δ ≤ ((RadialLine.trainingOnLine (outsideAt x S (O x)) l.val).card:ℝ) :=
        Nat.ceil_le.mp hr
      have hh := (div_le_iff₀ hδ).mp hr'
      rw [mul_comm] at hh
      change a ≤ δ*((((outsideAt x S (O x)).filter
        fun y => y.val.submodule ≤ l.val.val)).card:ℝ) at hh
      rwa [outsideAt_filter_card] at hh⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : G => z.val) he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DimensionThreePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem pair_count_three (hdim : finrank K V = 4)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) {δ a : ℝ} (hδ : 0<δ) :
    (pairs x X F δ a).card ≤
      (richRadials x X ⊤ ⌈a/δ⌉₊).card*(Nat.card K+1)^2 := by
  have hh := dominant_pair_count x (d := 3) hdim X F hF
    (pairs x X F δ a) (Finset.filter_subset _ _) ⌈a/δ⌉₊ (by
      intro p hp
      obtain ⟨hp,hne,hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨hA,hB⟩ := Finset.mem_product.mp hp
      obtain ⟨l,hl,hX⟩ := intersection_radial_three x hdim p.1 p.2 (hF _ hA) (hF _ hB)
        (hxF _ hA) (hxF _ hB) hne X
      refine ⟨l,hl.le,?_⟩
      rw [hX]
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hδ).mpr
      simpa only [mul_comm] using hs)
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add,add_comm] using hh

end SharpRamseyFive.WeightedOverlap
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_count_three (hdim : finrank K V=4)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H∈F,Incident x H) (a : ℝ) :
    (Finset.univ.filter (fun p : WeightedPrograms.DistinctPairs F =>
      a≤WeightedPrograms.strength (pencilLines x F) (radialWeight x X δ) p)).card ≤
      (ActualOverlap.richRadials x X ⊤ ⌈a/(δ:ℝ)⌉₊).card*(Nat.card K+1)^2 := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdimG (A : Submodule K V) (hA : A∈G) : finrank K A=3 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A : Submodule K V) (hA : A∈G) : x.submodule≤A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  exact (pair_strength_count_le x X δ F hF a).trans
    (WeightedOverlap.pair_count_three x hdim X G hdimG hxG (by exact_mod_cast hδ))

end
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pairs_three_off_radial (hdim : finrank K V = 4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (a D : ℝ) (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a Lines Q D) :
    ((Finset.univ.filter (fun p : DistinctPairs F  =>  a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) ≤
      D*((Nat.card K:ℝ)+1)^2 := by
  have hlocal : ((localLines S O δ a Lines x).card:ℝ) < D := by
    by_contra hn
    exact hgood (Finset.mem_filter.mpr ⟨hx,le_of_not_gt hn⟩)
  have hh := score_pair_count_three x hdim (outsideAt x S (O x)) δ hδ F hF a
  have hr := richRadials_le_localLines x S O δ a (by exact_mod_cast hδ) Lines hLines
  have hc : ((Finset.univ.filter (fun p : DistinctPairs F  =>  a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) ≤
      (localLines S O δ a Lines x).card*((Nat.card K:ℝ)+1)^2 := by
    exact_mod_cast hh.trans (Nat.mul_le_mul_right _ hr)
  exact hc.trans (mul_le_mul_of_nonneg_right hlocal.le (sq_nonneg _))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MomentWeightedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_weighted_cover (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K := by
  have hp (v : α) : x v^K≤∑ i∈T,if a i≤x v then (2*a i)^K else 0 := by
    by_cases hv : 0<x v
    · obtain ⟨i,hi,hix,hxi⟩:=hcover v hv
      apply (pow_le_pow_left₀ (hx v) hxi K).trans
      have hs:=Finset.single_le_sum (f := fun j => if a j≤x v then (2*a j)^K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa only [ite_eq_left hix] using hs
    · have hz : x v=0 := le_antisymm (le_of_not_gt hv) (hx v)
      rw [hz,zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hp v)).trans_eq
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ v,if a i≤x v then (2*a i)^K else 0)=
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*(2*a i)^K := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he,mul_pow]
  ring

end SharpRamseyFive.DyadicMoments

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OverlapDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in

lemma score_dyadic_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  change ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ mass (radialWeight x X δ)
    (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ∧
    mass (radialWeight x X δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ≤ 2*((δ:ℝ)*2^i)
  rw [mass_overlap x X δ F hF]
  unfold overlapDyads
  apply dyadic_cover δ _ (by positivity)
  · have hl:=overlap_pos_lower x X δ F hF p.1 p.2.val hp
    rwa [mass_overlap x X δ F hF] at hl
  · have hc : ((X.filter fun y => Incident y.val p.1.val ∧ Incident y.val p.2.val.val).card:ℝ) ≤
        (2:ℝ)^Nat.clog 2 X.card := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (Nat.le_pow_clog (by omega : 1<2) X.card)
    exact mul_le_mul_of_nonneg_left hc (by positivity)

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (A : ℝ) (hx : ∀ v,0 ≤ x v) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i ≤ x v ∧ x v ≤ 2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i ≤ x v).card:ℝ)*a i^K ≤ A) :
    (∑ v,x v^K) ≤ 2^K*T.card*A := by
  apply (moment_weighted_cover x a T K hK hx ha hcover).trans
  have hh := Finset.sum_le_sum (fun i hi => hcount i hi)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

theorem pow_sum_from_lower (x : α → ℝ) (m A : ℝ) (K R : ℕ) (hm0 : 0 ≤ m) (hKR : K ≤ R)
    (hx : ∀ v,0 ≤ x v) (hm : ∀ v,x v ≤ m) (hA : (∑ v,x v^K) ≤ A) :
    (∑ v,x v^R) ≤ m^(R-K)*A := by
  have hpow (v : α) : x v^R ≤ m^(R-K)*x v^K := by
    have he : R=(R-K)+K := by omega
    calc
      _ = x v^(R-K)*x v^K := by rw [←pow_add,←he]
      _  ≤  _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx v) (hm v) _) (pow_nonneg (hx v) _)
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpow v)).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hA (pow_nonneg hm0 _)

end SharpRamseyFive.DyadicMoments
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma boundedOverlapDyads_card (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (m : ℝ) :
    (boundedOverlapDyads x X δ m).card ≤ Nat.clog 2 X.card+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

omit [FiniteDimensional K V] [Finite K] in
lemma strength_le_typical_cap (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) : strength (pencilLines x F) (radialWeight x X δ) p ≤ m := by
  apply le_trans _ (hm p.1)
  change mass _ (_ ∩ _) ≤ mass _ _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
  intro d _ _
  exact NNReal.coe_nonneg _

omit [Finite K] in
lemma bounded_overlap_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈boundedOverlapDyads x X δ m,
      (δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  obtain ⟨i,hi,hlo,hhi⟩ := score_dyadic_cover x X δ hδ F hF p hp
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (strength_le_typical_cap x X δ F m hm p)⟩,hlo,hhi⟩

omit [Finite K] in

theorem score_polynomial_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (m A : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : k≠0)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (hcount : ∀ i∈boundedOverlapDyads x X δ m,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^k) ≤
      2^k*(Nat.clog 2 X.card+1)*A := by
  apply (moment_polynomial_tail _ _ (boundedOverlapDyads x X δ m) k hk A
    (strength_nonneg _ _) (by intro i _; positivity)
    (bounded_overlap_cover x X δ hδ F hF m hm) hcount).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by exact_mod_cast boundedOverlapDyads_card x X δ m) (by positivity)) hA

omit [Finite K] in

theorem score_higher_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (A : ℝ) (hA : 0 ≤ A) (k R : ℕ) (hk : k≠0) (hkR : k ≤ R)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hcount : ∀ i∈boundedOverlapDyads x X δ 2,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^R) ≤
      2^R*(Nat.clog 2 X.card+1)*A := by
  have hh := pow_sum_from_lower _ 2 _ k R (by norm_num) hkR
    (strength_nonneg (pencilLines x F) (radialWeight x X δ))
    (strength_le_typical_cap x X δ F 2 hm)
    (score_polynomial_power x X δ hδ F hF 2 A hA k hk hm hcount)
  apply hh.trans_eq
  rw [←mul_assoc,←mul_assoc,←pow_add,Nat.sub_add_cancel hkR]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LowMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma power_tail_card {T : Type*} [Fintype T] (f : T→ℝ) (hf : ∀ z,0 ≤ f z)
    (k : ℕ) (t M : ℝ) (ht : 0 < t) (hM : (∑ z,f z^k) ≤ M) :
    ((Finset.univ.filter fun z => t ≤ f z).card:ℝ) ≤ M/t^k := by
  apply (le_div_iff₀ (pow_pos ht k)).mpr
  calc
    _ = ∑ z∈Finset.univ.filter (fun z => t ≤ f z),t^k := by simp
    _ ≤ ∑ z∈Finset.univ.filter (fun z => t ≤ f z),f z^k := by
      apply Finset.sum_le_sum
      intro z hz
      exact pow_le_pow_left₀ ht.le (Finset.mem_filter.mp hz).2 k
    _ ≤ ∑ z,f z^k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro z _ _; exact pow_nonneg (hf z) k)
    _ ≤ M := hM

end SharpRamseyFive.ScoreGeometry

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OutsideCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_card_le (S O : Finset (ℙ K V)) : (outsideAt x S O).card ≤ S.card := by
  unfold outsideAt
  rw [Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_card Finset.sdiff_subset)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma boundedOverlapDyads_subset (x : ℙ K V) (S O : Finset (ℙ K V)) (δ : ℝ≥0) :
    boundedOverlapDyads x (outsideAt x S O) δ 2⊆strengthDyads S.card δ := by
  intro i hi
  obtain ⟨hi,hcap⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨?_,hcap⟩
  apply Finset.mem_range.mpr
  exact (Finset.mem_range.mp hi).trans_le
    (Nat.add_le_add_right (Nat.clog_mono_right 2 (outsideAt_card_le x S O)) 1)

lemma off_radialExceptions (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ)
    (x : ℙ K V) (hx : x∉radialExceptions S O δ Lines Q q n χ) :
    ∀i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q
        (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100) := by
  intro i hi hh
  exact hx (Finset.mem_biUnion.mpr ⟨i,boundedOverlapDyads_subset x S (O x) δ hi,hh⟩)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PowerValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma power_tail_mul {T : Type*} [Fintype T] (f : T→ℝ) (hf : ∀z,0 ≤ f z)
    (k : ℕ) (t M : ℝ) (ht : 0 < t) (hM : (∑z,f z^k) ≤ M) :
    ((Finset.univ.filter fun z => t ≤ f z).card:ℝ)*t^k ≤ M := by
  exact (le_div_iff₀ (pow_pos ht k)).mp (power_tail_card f hf k t M ht hM)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in
lemma validation_pairs_from_power (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (k : ℕ) (M : ℝ)
    (hM : (∑z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k) ≤ M)
    (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter fun z : {z : F×F // z.1 ≠ z.2} => t ≤
      mass (radialWeight x X δ) (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*t^k ≤ M := by
  let f : {z : F×F // z.1 ≠ z.2}→DistinctPairs F := fun z => ⟨z.val.1,⟨z.val.2,z.property.symm⟩⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact congrArg (fun z : DistinctPairs F => (z.1,z.2.val)) he
  have hc : (Finset.univ.filter fun z : {z : F×F // z.1 ≠ z.2} => t ≤
      mass (radialWeight x X δ) (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card ≤
      (Finset.univ.filter fun z : DistinctPairs F => t ≤
      strength (pencilLines x F) (radialWeight x X δ) z).card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
    · exact hf.injOn
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (pow_nonneg ht.le _)).trans
    (power_tail_mul _ (strength_nonneg _ _) k t M ht hM)

end

section

open Filter ParameterHierarchy
open scoped Topology

theorem eventually_dyad_power_payment {η : ℝ} (hη : 0 < η) (hη' : η < 1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D R χ : ℝ) (m : ℕ),Range η σ D R →
      χ ≤ P η σ D R/200 → (m:ℝ) ≤ Real.exp (3*σ) →
      2^200*((Nat.clog 2 m:ℝ)+1)*Real.exp (2*χ) ≤ Real.exp (P η σ D R/50) := by
  have he := eventually_power_absorption hη hη' (8*2^200) 1 (1/100)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),he] with σ hσ he
  intro D R χ m hr hχ hm
  have hh : (8*2^200:ℝ)*σ ≤ Real.exp (P η σ D R/100) := by
    simpa only [Real.rpow_one,one_mul,one_div,div_eq_mul_inv,mul_comm (100⁻¹:ℝ)] using he D R hr
  calc
    _ ≤ ((8*2^200:ℝ)*σ)*Real.exp (2*χ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith only [dyad_count_le hσ hm]
    _ ≤ Real.exp (P η σ D R/100)*Real.exp (P η σ D R/100) :=
      mul_le_mul hh (Real.exp_le_exp.mpr (by linarith only [hχ])) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add];congr 1;ring

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_pair_three_half_normalized (hdim : finrank K V = 4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hχ : (4*2^200:ℝ) ≤ Real.exp χ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) Lines Q ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)) :
    ((Finset.univ.filter (fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^3/n)^2*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : ((Nat.card K:ℝ)+1)^2 ≤ 4*(Nat.card K:ℝ)^2 := by nlinarith
  have hc : ((Finset.univ.filter (fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) ≤
      ((Finset.univ.filter (fun p : DistinctPairs F => a/2 ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p)).card:ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith only [ha,(Finset.mem_filter.mp hp).2]⟩
  have hh := hc.trans (score_pairs_three_off_radial x hdim S O δ hδ F hF (a/2) _ Lines hLines Q hx hgood)
  have hp : a^100 ≤ (2:ℝ)^100 := pow_le_pow_left₀ ha.le ha2 _
  calc
    _  ≤  ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)*((Nat.card K:ℝ)+1)^2*a^200 :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _  ≤  ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)*(4*(Nat.card K:ℝ)^2)*a^200 := by gcongr
    _ = ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^100*a^100) := by field_simp
    _  ≤  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^100*2^100) := by gcongr
    _ = ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*(4*2^200) := by ring
    _  ≤  ((Nat.card K:ℝ)^3/n)^2*Real.exp χ*Real.exp χ := by gcongr
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

theorem score_pair_three_moment (hdim : finrank K V=4)
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (n χ : ℝ) (hn : 0<n) (hχ : (4*2^200:ℝ) ≤ Real.exp χ)
    (Lines : Finset (Submodule K V)) (hLines : ∀l : RadialLine x,l.val∈Lines)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hm : ∀H:F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hgood : x∉radialExceptions S O δ Lines Q (Nat.card K) n χ)
    (R : ℕ) (hR : 200 ≤ R) :
    (∑z : DistinctPairs F,strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) z^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^3/n)^2*Real.exp (2*χ)) := by
  apply score_higher_power x _ δ hδ F hF _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  exact score_pair_three_half_normalized x hdim S O δ hδ F hF n _ χ hn (by positivity)
    (Finset.mem_filter.mp hi).2 hχ Lines hLines Q hx
    (off_radialExceptions S O δ Lines Q (Nat.card K) n χ x hgood i hi)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_OwnFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity

section
open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma cellMass_mono {A B : Finset (ℙ K V)} (hAB : A ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) : cellMass A δ H ≤ cellMass B δ H := by
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hAB))

lemma cellMass_union (A B : Finset (ℙ K V)) (δ : ℝ) (H : ℙ K (Dual K V)) :
    cellMass (A∪B) δ H = cellMass A δ H+cellMass B δ H-cellMass (A∩B) δ H := by
  have he := Finset.card_union_add_card_inter
    (A.filter fun y => Incident y H) (B.filter fun y => Incident y H)
  have he' : (((A∪B).filter fun y => Incident y H).card:ℝ)+
      ((A∩B).filter fun y => Incident y H).card =
        (A.filter fun y => Incident y H).card+(B.filter fun y => Incident y H).card := by
    rw [Finset.filter_union,Finset.filter_inter_distrib]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma filter_sdiff_eq {α : Type*} [DecidableEq α] (S O : Finset α)
    (p : α→Prop) [DecidablePred p] : (S\O).filter p = S.filter p\O.filter p := by
  ext y
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto

lemma cellMass_sdiff {S O : Finset (ℙ K V)} (hOS : O ⊆ S) (δ : ℝ)
    (H : ℙ K (Dual K V)) : cellMass (S\O) δ H = cellMass S δ H-cellMass O δ H := by
  have he := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (fun y => Incident y H) hOS)
  have he' : (((S\O).filter fun y => Incident y H).card:ℝ)+
      (O.filter fun y => Incident y H).card = (S.filter fun y => Incident y H).card := by
    rw [filter_sdiff_eq]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma cellMass_erase (S : Finset (ℙ K V)) (x : ℙ K V) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) :
    0 ≤ cellMass S δ H-cellMass (S\{x}) δ H ∧
      cellMass S δ H-cellMass (S\{x}) δ H ≤ δ := by
  have hl := cellMass_mono (Finset.sdiff_subset : S\{x} ⊆ S) hδ H
  have hc : (S.filter fun y => Incident y H).card ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by
    rw [filter_sdiff_eq]
    have h := Finset.card_le_card_sdiff_add_card (s:=S.filter fun y => Incident y H)
      (t:=({x}:Finset (ℙ K V)).filter fun y => Incident y H)
    have h1 : (({x}:Finset (ℙ K V)).filter fun y => Incident y H).card ≤ 1 :=
      (Finset.card_filter_le ..).trans_eq (Finset.card_singleton x)
    omega
  have hc' : ((S.filter fun y => Incident y H).card:ℝ) ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by exact_mod_cast hc
  constructor
  · exact sub_nonneg.mpr hl
  · have hm := mul_le_mul_of_nonneg_left hc' hδ
    unfold cellMass
    nlinarith only [hm]

variable [Finite K] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
lemma typical_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (j : Option J) : |deviation S C j H| ≤ threshold j := by
  by_contra hn
  exact hH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,lt_of_not_ge hn⟩)

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma queryLoss_bounds (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) :
    0 ≤ queryLoss S O x H ∧ queryLoss S O x H ≤ (Nat.card K:ℝ)/S.card := by
  have h := cellMass_erase (S\O) x (show 0 ≤ (Nat.card K:ℝ)/S.card by positivity) H
  have he : (S\O)\{x}=S\(O∪{x}) := by
    ext y
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  simpa only [queryLoss,outsideMass,he] using h

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma outsideMass_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) (H : ℙ K (Dual K V)) :
    outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b)) =
      deviation S C none H-deviation S C (some a) H-deviation S C (some b) H+
        deviation S C (some c) H-queryLoss S (C a∪C b) x H := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast hS.card_pos.ne'
  have hmass := cellMass_sdiff (Finset.union_subset ha hb) ((Nat.card K:ℝ)/S.card) H
  rw [cellMass_union] at hmass
  have hcard : ((C a∪C b).card:ℝ)+((C a∩C b).card:ℝ)=(C a).card+(C b).card := by
    exact_mod_cast Finset.card_union_add_card_inter (C a) (C b)
  simp only [deviation,familyCell,queryLoss,ownFraction,div_self hn,hc]
  rw [hmass]
  have hs := congrArg (fun z : ℝ => z/(S.card:ℝ)) hcard
  simp only [add_div] at hs
  linarith only [hs]

omit [Finite K] in

theorem typical_mass_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (hf : ownFraction S (C a) (C b) ≤ 2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1/100) :
    3/4 ≤ outsideMass S (C a∪C b) x H ∧
    |outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b))| ≤ 17/100 ∧
    outsideMass S (C a∪C b) x H ≤ 11/10 := by
  have h0 := typical_deviation S C hH none
  have h1 := typical_deviation S C hH (some a)
  have h2 := typical_deviation S C hH (some b)
  have h3 := typical_deviation S C hH (some c)
  simp only [threshold,abs_le] at h0 h1 h2 h3
  have hl := queryLoss_bounds S (C a∪C b) x H
  have he := outsideMass_deviation S C hS a b c ha hb hc x H
  have hmass : outsideMass S (C a∪C b) x H ≤ cellMass S ((Nat.card K:ℝ)/S.card) H :=
    cellMass_mono Finset.sdiff_subset (by positivity) H
  have hbase : deviation S C none H=cellMass S ((Nat.card K:ℝ)/S.card) H-1 := by
    simp only [deviation,familyCell,div_self (show (S.card:ℝ)≠0 by exact_mod_cast hS.card_pos.ne')]
  rw [hbase] at h0
  refine ⟨?_,⟨?_,?_⟩⟩
  · linarith
  · rw [abs_le]; constructor <;> linarith
  · linarith

end

open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical

end SharpRamseyFive.ScoreRegularity

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

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma mass_outside_pencil (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) :
    mass (radialWeight x (outsideAt x S O) (pointStrength S)) (pencilLines x F H) =
      outsideMass S O x H.val := by
  rw [mass_pencil x (outsideAt x S O) (pointStrength S) F hF H]
  change _*(((outsideAt x S O).filter fun y => y.val.submodule≤LinearMap.ker H.val.rep).card:ℝ)=_
  rw [outsideAt_filter_card,coe_pointStrength]
  rfl

omit [Finite K] [Fintype (ℙ K V)] in
theorem actual_radial_mass_bounds {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (hS : S.Nonempty)
    (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100) (H : F) :
    3/4 ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H) ∧
    |mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)-
      (1-ownFraction S (C a) (C b))|≤17/100 ∧
    mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)≤11/10 := by
  rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1)]
  exact typical_mass_bounds S C hS a b c ha hb hc x (hF H.val H.property).2 hf hn

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

lemma integral_failureCount (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Finset X) (P : X→Ω→Prop) :
    (∫ω,failureCount U P ω ∂μ)=∑x∈U,μ.real {ω | P x ω} := by
  have he : failureCount U P=fun ω =>∑x∈U,({ω | P x ω}).indicator (fun _ => (1:ℝ)) ω := by
    funext ω
    simp only [failureCount,Set.indicator_apply,Set.mem_ofPred_eq,Finset.sum_boole]
  rw [he,integral_finsetSum U (fun x _ => (integrable_const (1:ℝ)).indicator
    (Set.to_countable _ |>.measurableSet))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_indicator_const (1:ℝ) (Set.to_countable _ |>.measurableSet)]
  simp

theorem expected_failureCount_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U bad : Finset X) (P : X→Ω→Prop) (a : X→ℝ) {ε : ℝ}
    (hε : 0≤ε) (ha : ∀x∈U,0≤a x)
    (hprob : ∀x∈U\bad,μ.real {ω | P x ω}≤ε+a x) :
    (∫ω,failureCount U P ω ∂μ)≤bad.card+(U.card:ℝ)*ε+∑x∈U,a x := by
  rw [integral_failureCount]
  calc
    _ ≤ ∑x∈U,((if x∈bad then (1:ℝ) else 0)+ε+a x) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hb : x∈bad
      · simp only [hb,ite_true]
        exact measureReal_le_one.trans (by linarith only [hε,ha x hx])
      · simp only [hb,ite_false,zero_add]
        exact hprob x (Finset.mem_sdiff.mpr ⟨hx,hb⟩)
    _ = ((U.filter fun x => x∈bad).card:ℝ)+(U.card:ℝ)*ε+∑x∈U,a x := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp only [Finset.sum_boole,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hc : ((U.filter fun x => x∈bad).card:ℝ)≤bad.card := Nat.cast_le.mpr
        (Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2))
      linarith only [hc]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

end SharpRamseyFive.PoissonScore

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionThreeTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem eventually_three_validation_tail {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (O : ℙ K V→Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
      (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (t : ℝ),
      finrank K V=4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      O x=C a∪C b → (S.card:ℝ) ≤ 10*Real.exp (2*σ) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=3) S C ((L₀:ℝ)/100) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) →
      scale (K:=K) 3 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        Real.exp (-P η σ D R/2) := by
  have ht := eventually_validation_original_tail hη hη' Cb hCb
  have hd := eventually_dyad_power_payment hη hη'
  have hc := eventually_power_absorption hη hη' (4*2^200) 0 (1/200)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc] with σ hσ ht hd hc
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c O F Lines Q t
    hdim hq hr hL hb₀ hbhi hτ hS ha hb hC hO hSn hn hf hF hx hLines hxQ hgood ht₀
  have hS0 : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hδ : 0 < pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength]
    exact div_pos (by exact_mod_cast Nat.card_pos (α:=K)) hS0
  have hlarge : (4*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (200⁻¹:ℝ)] using hc D R hr
  have hcard : ((outsideAt x S (O x)).card:ℝ) ≤ Real.exp (3*σ) := by
    have he : (10:ℝ) ≤ Real.exp σ := by linarith [Real.add_one_le_exp σ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr (outsideAt_card_le x S (O x))
      _ ≤ 10*Real.exp (2*σ) := hSn
      _ ≤ Real.exp σ*Real.exp (2*σ) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm (H:F) : mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H) ≤ 2 := by
    rw [hO]
    exact (actual_radial_mass_bounds x S C hS a b c ha hb hC F hF hf hn H).2.2.trans (by norm_num)
  have hh := score_pair_three_moment x hdim S O (pointStrength S) hδ F
    (fun H hH => (hF H hH).1) S.card (P η σ D R/200) hS0 hlarge Lines hLines Q hxQ hm hgood 200 (le_refl _)
  have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
  have hmoment : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200) ≤
        (scale (K:=K) 3 S.card)^2*Real.exp (P η σ D R/50) := by
    apply hh.trans
    change 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
      (((Nat.card K:ℝ)^3/S.card)^2*Real.exp (2*(P η σ D R/200))) ≤ _
    calc
      _ = ((Nat.card K:ℝ)^3/S.card)^2*(2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
          Real.exp (2*(P η σ D R/200))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
  have hpairs (u : ℝ) (hu : 0 < u) (_hu2 : u ≤ 2) :=
    validation_pairs_from_power x (outsideAt x S (O x)) (pointStrength S) F 200 _ hmoment u hu
  simp only [hO] at hpairs
  exact ht 3 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
    ha hb hC (by convert hSn using 1; norm_num; ring) hn hf hF hx hpairs ht₀

end

open Module ProjectiveIncidence CellVariance ScoreRegularity GlobalRadial PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_CellScoreProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma exp_sub_le_scaled {a b C : ℝ} (hC : 0<C) (h : a+Real.log C≤b) :
    C*Real.exp (-b)≤Real.exp (-a) := by
  rw [←Real.exp_log hC,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [h])

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptionScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars
lemma regular_training_payment_half {L P : ℝ} (hL : 10000000000≤L) (hLP : 100*L≤P) :
    200000*Real.exp (-2*(L/100))+Real.exp (-P/2)≤Real.exp (-L/1000)/2 := by
  have h₁ := exp_sub_le_scaled (a:=L/1000) (b:=2*(L/100)) (C:=800000) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤800000),hL])
  have h₂ := exp_sub_le_scaled (a:=L/1000) (b:=P/2) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hL,hLP])
  simp only [neg_div,neg_mul] at *
  linarith only [h₁,h₂]

lemma ambient_three_payment {σ : ℝ} (hσ : 100≤σ) :
    2*Real.exp (3*σ)*(Real.exp σ)^(-(50:ℝ))≤1/2 := by
  rw [←Real.exp_mul, mul_assoc,←Real.exp_add]
  have h := exp_sub_le_scaled (a:=0) (b:=47*σ) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hσ])
  simp only [neg_zero,Real.exp_zero] at h
  have he : 3*σ+σ*(-50)=-(47*σ) := by ring
  rw [he]
  linarith only [h]

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_DimensionTwoIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

lemma integral_filter_card_le {Ω A : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] [DecidableEq A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U bad : Finset A) (E : A→Set Ω) {e : ℝ} (he : 0≤e)
    (hprob : ∀x∈U\bad,μ.real (E x)≤e) :
    (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)≤(bad.card:ℝ)+U.card*e := by
  have h := expected_failureCount_le μ U bad (fun x ω => ω∈E x) (fun _ => 0) he
    (fun _ _ => le_rfl) (fun x hx => by
      simpa only [add_zero,Set.ofPred_mem_eq] using
        hprob x (by simpa only [Finset.mem_sdiff] using hx))
  simpa only [failureCount,Finset.sum_const_zero,add_zero] using h

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

lemma off_ambientStrongExceptions {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V]
    (σ P : ℝ) (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (x : ℙ K V)
    (hx : x∉ambientStrongExceptions σ P S O Lines Q) :
    x∉badCenters S O (pointStrength S) (1/(100*(momentOrder σ P:ℝ))) Lines Q 1 ∨
      (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P) := by
  by_cases h : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P)
  · exact Or.inr h
  · exact Or.inl (by simpa only [ambientStrongExceptions,ite_eq_right h] using hx)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

lemma mem_radialInventory {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (ℙ K V)] [∀x : ℙ K V,Fintype (RadialLine x)]
    (x : ℙ K V) (l : RadialLine x) : l.val∈radialInventory (K:=K) (V:=V) := by
  exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩⟩

lemma radialInventory_rank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (ℙ K V)] [∀x : ℙ K V,Fintype (RadialLine x)]
    (l : Submodule K V) (hl : l∈radialInventory (K:=K) (V:=V)) : finrank K l=2 := by
  obtain ⟨x,_,hl⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hl
  exact r.property.1

theorem eventually_three_score_integrals_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ {A : Type} [Fintype A] (g : ℝ) (F : Finset J) (hF : F.Nonempty)
      (Flat : J→Submodule K (I→K)) (X U S : Finset (ℙ K (I→K)))
      (t₀ : ℝ) (ht₀ : 0<t₀) (rawOwn : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (C : A→Finset (ℙ K (I→K))) (ia ib ic : ℙ K (I→K)→A),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → g≤2*σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (X.card:ℝ)≤Real.exp (3*σ/2+g) →
      t₀=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5) →
      S=peelSet (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀) →
      Real.exp (3*σ/2+g)/4≤S.card → (S.card:ℝ)≤10*Real.exp (2*σ) →
      (∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
        (peelLength (P η σ D R/10000<g) F hF (fun j => flatPoints (Flat j)) X ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀)) x⊆rawOwn x) →
      (∀x,S∩rawOwn x=C (ia x)∪C (ib x)) →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let O := fun x => C (ia x)∪C (ib x)
      let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
      let t := scale (K:=K) 3 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
      (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
      (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (8*P η σ D R) := by
  have ht := eventually_three_validation_tail hη hη' Cb hCb
  have hu := eventually_three_ambient_tail_cases hη hη' Cb hCb
  have he := eventually_literal_plane_exceptions hη hη'
  have hm := eventually_score_margins hη hη' Cb hCb
  have hl := eventually_hierarchy hη hη' Cb 1 10000000000 hCb (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hu,he,hm,hl] with σ hσ ht hu he hm hl
  intro D b₀ τ R L₀ q K I J _ _ _ _ _ _ _ _ A _ g F hF Flat X U S t₀ ht₀ rawOwn C ia ib ic
    hq hcard hσq hI hr hL hb₀ hbhi hτ hg hFlat hcover hX htc hpeel hquarter hn hraw hOwn hC hCS hCc hdiv hf
  dsimp only
  let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
  let O := fun x => C (ia x)∪C (ib x)
  let O' := fun x => S∩rawOwn x
  let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let t := scale (K:=K) 3 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
  let Lines := radialInventory (K:=K) (V:=I→K)
  let reg := irregular (d:=3) S C ((L₀:ℝ)/100)
  let rad := radialExceptions S O' (pointStrength S) Lines Finset.univ q S.card (P η σ D R/200)
  let strong := ambientStrongExceptions σ (P η σ D R) S O' Lines Finset.univ
  let bad := reg∪rad
  let E : ℙ K (I→K)→Set (Fin R→S→ℕ) := fun x =>
    {ω | Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\exceptional S C) (ctr x) ω|}
  have hSn0 : (0:ℝ)<S.card := (by positivity : (0:ℝ)<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn0)
  have hn1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hdim : finrank K (I→K)=4 := by simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hI
  have hqσ : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hSn : (S.card:ℝ)≤Real.exp (3*σ) := by
    have hx : (10:ℝ)≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
    calc
      _≤10*Real.exp (2*σ) := hn
      _≤Real.exp σ*Real.exp (2*σ) := mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
      _=_ := by rw [←Real.exp_add];congr 1;ring
  have he := he D R hr q K I J g F hF Flat X S t₀ ht₀ rawOwn Lines Finset.univ
    hq hcard hσq (Or.inl hI) hg hFlat hcover hX htc hpeel hquarter hSn hraw radialInventory_rank
  have hrad : (rad.card:ℝ)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000)/2 := by simpa only [hL] using he.1
  have hstrong : (strong.card:ℝ)≤(S.card:ℝ)*Real.exp (7*P η σ D R) := he.2
  have hlarge : 10000000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b₀ τ hr hbhi hτ).1
  have hLP : 100*(L₀:ℝ)≤P η σ D R := by rw [hL];exact (hm D b₀ τ R hr hb₀ hbhi hτ).2.2.2.1
  have hreg := irregular_card_bound (d:=3) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have hbad : (bad.card:ℝ)≤200000*(S.card:ℝ)*Real.exp (-2*((L₀:ℝ)/100))+
      (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000)/2 := by
    exact (Nat.cast_le.mpr (Finset.card_union_le reg rad) |>.trans (by norm_cast)).trans (add_le_add hreg hrad)
  have hpay : (bad.card:ℝ)+S.card*Real.exp (-P η σ D R/2)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) := by
    have hh := mul_le_mul_of_nonneg_left (ScoreScalars.regular_training_payment_half hlarge hLP) hSn0.le
    nlinarith only [hh,hbad]
  have hbelow (x : ℙ K (I→K)) (H : ℙ K (Dual K (I→K))) (hH : H∈pencil x\exceptional S C) :
      Incident x H ∧ H∉exceptional S C := by
    have hh := Finset.mem_sdiff.mp hH
    exact ⟨(Finset.mem_filter.mp hh.1).2,hh.2⟩
  have htraining (x : ℙ K (I→K)) (hx : x∉bad) : μ.real (E x)≤Real.exp (-P η σ D R/2) := by
    have hx' : x∉reg ∧ x∉rad := ⟨fun h => hx (Finset.mem_union_left _ h),fun h => hx (Finset.mem_union_right _ h)⟩
    apply ht D b₀ τ R L₀ K (I→K) x S C (ia x) (ib x) (ic x) O' (pencil x\exceptional S C)
      Lines Finset.univ t hdim hqσ hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) (hOwn x) hn hdiv (hf x)
      (hbelow x) hx'.1 (mem_radialInventory x) (Finset.mem_univ _) _ (le_refl _)
    simpa only [hcard] using hx'.2
  have hambient (x : ℙ K (I→K)) (hx : x∉bad∪strong) : μ.real (E x)≤(Nat.card K:ℝ)^(-(50:ℝ)) := by
    have hh : x∉bad ∧ x∉strong := ⟨fun h => hx (Finset.mem_union_left _ h),fun h => hx (Finset.mem_union_right _ h)⟩
    have hx' : x∉reg ∧ x∉rad := ⟨fun h => hh.1 (Finset.mem_union_left _ h),fun h => hh.1 (Finset.mem_union_right _ h)⟩
    apply hu D b₀ τ R L₀ K (I→K) x S C (ia x) (ib x) (ic x) O' (pencil x\exceptional S C)
      Lines Finset.univ t hdim hqσ hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) (hOwn x) hn hdiv (hf x)
      (hbelow x) hx'.1 (mem_radialInventory x) (Finset.mem_univ _) _
      (off_ambientStrongExceptions σ (P η σ D R) S O' Lines Finset.univ x hh.2) (le_refl _)
    simpa only [hcard] using hx'.2
  constructor
  · have hh := integral_filter_card_le μ S bad E (Real.exp_nonneg _) (fun x hx => htraining x (Finset.mem_sdiff.mp hx).2)
    change (∫ω,((S.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans ?_ hpay
    convert hh using 1; try rfl
    apply integral_congr_ae
    filter_upwards with ω
    congr 2
    ext x
    simp only [Finset.mem_filter]
  · have hh := integral_filter_card_le μ U (bad∪strong) E (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun x hx => hambient x (Finset.mem_sdiff.mp hx).2)
    change (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=((bad∪strong).card:ℝ)+U.card*(Nat.card K:ℝ)^(-(50:ℝ))) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      congr 2
      ext x
      simp only [Finset.mem_filter]
    have hq2 : (2:ℝ)≤Nat.card K := by rw [hqσ];linarith only [Real.add_one_le_exp σ,hσ]
    have hU : (U.card:ℝ)≤2*Real.exp (3*σ) := by
      have hp := Finset.card_le_univ U
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K (I→K) hdim] at hp
      norm_num [Finset.sum_range_succ] at hp
      have hh : (U.card:ℝ)≤1+Nat.card K+(Nat.card K:ℝ)^2+(Nat.card K:ℝ)^3 := by exact_mod_cast hp
      have hqpow : (Nat.card K:ℝ)^3=Real.exp (3*σ) := by rw [hqσ,←Real.exp_nat_mul];norm_num
      rw [←hqpow]
      have hqq : (Nat.card K:ℝ)^2≥2*Nat.card K := by nlinarith only [hq2]
      nlinarith only [hh,hq2,hqq,mul_le_mul_of_nonneg_right hqq (by linarith only [hq2] : (0:ℝ)≤Nat.card K)]
    have hu : (U.card:ℝ)*(Nat.card K:ℝ)^(-(50:ℝ))≤1/2 := by
      rw [hqσ]
      exact (mul_le_mul_of_nonneg_right hU (by positivity)).trans (ScoreScalars.ambient_three_payment hσ)
    have hbadn : (bad.card:ℝ)≤S.card := by
      have hexp : Real.exp (-(L₀:ℝ)/1000)≤1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L₀.coe_nonneg) (by norm_num))
      have htpos : 0≤(S.card:ℝ)*Real.exp (-P η σ D R/2) := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
      have hb : (bad.card:ℝ)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) := by linarith only [hpay,htpos]
      exact hb.trans (mul_le_of_le_one_right hSn0.le hexp)
    have hP0 : 0≤P η σ D R := by linarith only [hLP,hlarge]
    have hPexp : (3:ℝ)≤Real.exp (P η σ D R) := by linarith only [Real.add_one_le_exp (P η σ D R),hLP,hlarge]
    have hexp7 : (1:ℝ)≤Real.exp (7*P η σ D R) := Real.one_le_exp (mul_nonneg (by norm_num) hP0)
    have hbadall : ((bad∪strong).card:ℝ)≤(S.card:ℝ)+(S.card:ℝ)*Real.exp (7*P η σ D R) := by
      have hc : ((bad∪strong).card:ℝ)≤(bad.card:ℝ)+strong.card := by exact_mod_cast Finset.card_union_le bad strong
      exact hc.trans (add_le_add hbadn hstrong)
    calc
      _≤(S.card:ℝ)+(S.card:ℝ)*Real.exp (7*P η σ D R)+1/2 := add_le_add hbadall hu
      _≤3*(S.card:ℝ)*Real.exp (7*P η σ D R) := by
        nlinarith only [mul_le_mul_of_nonneg_left hexp7 hSn0.le,hn1]
      _≤Real.exp (P η σ D R)*(S.card:ℝ)*Real.exp (7*P η σ D R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPexp (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _=_ := by rw [mul_assoc,mul_left_comm (Real.exp _),←Real.exp_add];congr 2;ring

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_three_score_integrals_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_three_score_integrals_oai
