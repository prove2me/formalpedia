-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:43:07.963023+00:00
-- url     : https://prove2.me/submissions/959199b2-b446-4b16-a50d-31a3c2caa007

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_validation_original_tail
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_low_original_tail

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

theorem card_hyperplanes [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} (l : RadialLine x) :
    Nat.card {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ↔ b.submodule ≤ l.val.dualAnnihilator := by
    rw [Projectivization.submodule_eq b, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq l.val
  rw [l.property.1] at h
  congr 2
  omega

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

variable [Finite K]

lemma one_anchor_count (F : Finset (ℙ K (Module.Dual K V))) (l : RadialLine x) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-2), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} := fun H =>
    ⟨H.val.val, (Finset.mem_filter.mp H.property).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} => b.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes l, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LowBudgetPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open scoped BigOperators

lemma lowMomentBudget_eq_high (Q M A B b L : ℝ) (p R N₁ N₂ : ℕ)
    (hB : B≠0) (hb : b≠0) : lowMomentBudget Q M A B b L p R N₁ N₂=
      highMomentBudget Q M A B b L p R N₂+
        B*((N₁:ℝ)/B)*(p:ℝ)^3*(200*p+2*((R:ℝ)*L)) := by
  unfold lowMomentBudget highMomentBudget certificateMajorant highCertificateMajorant
  push_cast
  field_simp [hB, hb]
  ring

lemma lowMomentBudget_le_poly (Q a s B b L : ℝ) (p R N₁ N₂ : ℕ)
    (hB : 1≤B) (hb : 0<b) (ha : 0≤a) (hL : 0≤L)
    (hroot : Q/(B*b^8)≤40) (hanchor : (N₂:ℝ)*b/B≤20) (hpair : Q/B^2≤400)
    (hone : (N₁:ℝ)/B ≤ s) :
    lowMomentBudget Q (a*B^2) (a*B) B b L p R N₁ N₂ ≤
      B*lowBudgetPoly a s p ((R:ℝ)*L) := by
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  rw [lowMomentBudget_eq_high _ _ _ _ _ _ _ _ _ _ hB0.ne' hb.ne']
  unfold lowBudgetPoly
  conv_rhs => rw [mul_add]
  apply add_le_add (highMomentBudget_le_poly Q a B b L p R N₂ hB hb ha hL hroot hanchor hpair)
  have hn := mul_le_mul_of_nonneg_left hone hB0.le
  have hp : 0≤(p:ℝ)^3*(200*p+2*((R:ℝ)*L)) := by positivity
  convert mul_le_mul_of_nonneg_right hn hp using 1 <;> ring

open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma lowBudgetPoly_bound {σ P p a s k c : ℝ} (hσ : 1≤σ)
    (hP : 0≤P) (hPhi : P≤σ) (hp : 0≤p) (hphi : p≤k*σ)
    (ha : 0≤a) (hahi : a ≤ c*σ*Real.exp (P/50))
    (hs : s≤4*Real.exp (P/10000)) (hk : 0≤k) (hc : 0 ≤ c) :
    lowBudgetPoly a s p P≤(highPolyConstant k c+4*k^3*(200*k+2))*σ^205*Real.exp (P/50) := by
  have hσ0 : 0≤σ := by linarith
  have hhigh := highBudgetPoly_bound hσ (Real.one_le_exp_iff.mpr (by positivity : 0≤P/50))
    hp hphi hP hPhi ha hahi hk hc
  have hpow : σ^(4:ℕ)≤σ^(205:ℕ) := pow_le_pow_right₀ hσ (by norm_num)
  have hE : Real.exp (P/10000)≤Real.exp (P/50) := Real.exp_le_exp.mpr (by linarith)
  have hterm : s*p^3*(200*p+2*P)≤(4*k^3*(200*k+2))*σ^205*Real.exp (P/50) := by
    calc
      _ ≤ (4*Real.exp (P/10000))*(k*σ)^3*((200*k+2)*σ) := by
        apply mul_le_mul (mul_le_mul hs (pow_le_pow_left₀ hp hphi 3) (by positivity) (by positivity))
          (by nlinarith only [hphi,hPhi]) (by positivity) (by positivity)
      _ = (4*k^3*(200*k+2))*σ^4*Real.exp (P/10000) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hE
        (Real.exp_nonneg _) (by positivity)
  unfold lowBudgetPoly
  calc
    _ ≤ highPolyConstant k c*σ^205*Real.exp (P/50)+
        (4*k^3*(200*k+2))*σ^205*Real.exp (P/50) := add_le_add hhigh hterm
    _ = _ := by ring

theorem eventually_low_poly_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (k c : ℝ) (hk : 0≤k) (hc : 0 ≤ c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R p a s : ℝ,Range η σ D R →
      0≤p → p≤k*σ → 0≤a → a ≤ c*σ*Real.exp (P η σ D R/50) →
      s≤4*Real.exp (P η σ D R/10000) →
      Real.exp (P η σ D R/50)+2*(p+1)*lowBudgetPoly a s p (P η σ D R)≤
        Real.exp (P η σ D R/5) := by
  let C := highPolyConstant k c+4*k^3*(200*k+2)
  have hC : 0<C := add_pos_of_pos_of_nonneg (highPolyConstant_pos hk hc) (by positivity)
  have hK : 0<1+2*(k+1)*C := by positivity
  have hab := eventually_power_absorption hη hη' (1+2*(k+1)*C) 206 (1/10)
    hK (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R p a s hr hp hphi ha hahi hsi
  have hpar := finite_bounds hη hη' hσ hr
  have hP : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hpar.2.2.2.2.2.1
  have hPhi : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hpol := lowBudgetPoly_bound hσ hP hPhi hp hphi ha hahi hsi hk hc
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

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open scoped BigOperators

lemma pencil_alphabet_exp {q k : ℕ} {σ : ℝ} (hk : 1≤k) (hσ : 0≤σ)
    (hq : (q:ℝ)=Real.exp σ) : (pencilAlphabet q k:ℝ)≤(k:ℝ)*Real.exp (((k:ℝ)-1)*σ) := by
  have hq1 : 1≤q := by exact_mod_cast (hq▸Real.one_le_exp_iff.mpr hσ)
  have hh := pencilAlphabet_le (k:=k) hq1
  rw [hq,←Real.exp_nat_mul,Nat.cast_sub hk,Nat.cast_one] at hh
  exact hh

lemma dimensional_budget_ratios {q d : ℕ} {σ n : ℝ} (hd : 2≤d) (hdhi : d≤4)
    (hσ : 20≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hnhi : n≤10*Real.exp (((d:ℝ)+1)*σ/2)) :
    1≤dimensionalScale q d n ∧
    (pencilAlphabet q d:ℝ)/(dimensionalScale q d n*(Real.exp (σ/5))^8)≤40 ∧
    (pencilAlphabet q (d-2):ℝ)*Real.exp (σ/5)/dimensionalScale q d n≤20 ∧
    (pencilAlphabet q d:ℝ)/(dimensionalScale q d n)^2≤400 := by
  let B := dimensionalScale q d n
  let a : ℝ := ((d:ℝ)-1)*σ/2
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hdRhi : (d:ℝ)≤4 := by exact_mod_cast hdhi
  have hσ0 : 0≤σ := by linarith
  have hlo : Real.exp a/10≤B := by
    unfold B dimensionalScale
    apply (le_div_iff₀ hn).mpr
    calc
      _ ≤ (Real.exp a/10)*(10*Real.exp (((d:ℝ)+1)*σ/2)) :=
        mul_le_mul_of_nonneg_left hnhi (by positivity)
      _ = Real.exp ((d:ℝ)*σ) := by
        rw [show (Real.exp a/10)*(10*Real.exp (((d:ℝ)+1)*σ/2))=
          Real.exp a*Real.exp (((d:ℝ)+1)*σ/2) by ring,←Real.exp_add]
        congr 1
        dsimp [a]
        ring
      _ = (q:ℝ)^d := by rw [hq,←Real.exp_nat_mul]
  have ha : 10≤a := by dsimp [a];nlinarith
  have hB1 : 1≤B := by have hh := Real.add_one_le_exp a;linarith
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB1
  have hQ : (pencilAlphabet q d:ℝ)≤4*Real.exp (((d:ℝ)-1)*σ) :=
    (pencil_alphabet_exp (by omega) hσ0 hq).trans
      (mul_le_mul_of_nonneg_right hdRhi (Real.exp_nonneg _))
  have hb8 : (Real.exp (σ/5))^8=Real.exp (8*σ/5) := by
    rw [←Real.exp_nat_mul];congr 1;norm_num;ring
  refine ⟨hB1,?_,?_,?_⟩
  · apply (div_le_iff₀ (mul_pos hB0 (pow_pos (Real.exp_pos _) _))).mpr
    calc
      _ ≤ 4*Real.exp (((d:ℝ)-1)*σ) := hQ
      _ ≤ 4*Real.exp (a+8*σ/5) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp [a]
        nlinarith
      _ = 40*((Real.exp a/10)*(Real.exp (σ/5))^8) := by rw [hb8,Real.exp_add];ring
      _ ≤ 40*(B*(Real.exp (σ/5))^8) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlo (by positivity)) (by norm_num)
  · by_cases hd2 : d=2
    · subst d
      norm_num [pencilAlphabet]
    have hdk : 1≤d-2 := by omega
    have hN : (pencilAlphabet q (d-2):ℝ)≤2*Real.exp (((d:ℝ)-3)*σ) := by
      have hh := pencil_alphabet_exp (k:=d-2) hdk hσ0 hq
      rw [Nat.cast_sub hd,Nat.cast_ofNat] at hh
      have he : (d:ℝ)-2-1=(d:ℝ)-3 := by ring
      rw [he] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
    apply (div_le_iff₀ hB0).mpr
    calc
      _ ≤ (2*Real.exp (((d:ℝ)-3)*σ))*Real.exp (σ/5) :=
        mul_le_mul_of_nonneg_right hN (Real.exp_nonneg _)
      _ = 2*Real.exp (((d:ℝ)-3)*σ+σ/5) := by rw [mul_assoc,←Real.exp_add]
      _ ≤ 2*Real.exp a := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp [a]
        nlinarith
      _ = 20*(Real.exp a/10) := by ring
      _ ≤ 20*B := mul_le_mul_of_nonneg_left hlo (by norm_num)
  · apply (div_le_iff₀ (sq_pos_of_pos hB0)).mpr
    calc
      _ ≤ 4*Real.exp (((d:ℝ)-1)*σ) := hQ
      _ = 400*(Real.exp a/10)^2 := by
        rw [div_pow,←Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show (2:ℝ)*a=((d:ℝ)-1)*σ by dsimp [a];ring]
        ring
      _ ≤ 400*B^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlo 2) (by norm_num)

lemma low_one_anchor_ratio {q d : ℕ} {σ n P : ℝ} (hd : 2≤d) (hdhi : d≤4)
    (hσ : 0≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hsmall : n≤(q:ℝ)^2*Real.exp (P/10000)) :
    (pencilAlphabet q (d-1):ℝ)/dimensionalScale q d n≤4*Real.exp (P/10000) := by
  have hq0 : 0<(q:ℝ) := hq▸Real.exp_pos _
  have hdR : (d:ℝ)≤4 := by exact_mod_cast hdhi
  have hB : 0<dimensionalScale q d n := div_pos (pow_pos hq0 _) hn
  have hN : (pencilAlphabet q (d-1):ℝ)≤4*(q:ℝ)^(d-2) := by
    have hh := pencilAlphabet_le (k:=d-1) (show 1≤q by exact_mod_cast (hq▸Real.one_le_exp_iff.mpr hσ))
    rw [Nat.sub_sub] at hh
    norm_num only [Nat.reduceAdd] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (by rw [Nat.cast_sub (by omega),Nat.cast_one];linarith) (by positivity)
  apply (div_le_iff₀ hB).mpr
  unfold dimensionalScale
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (4*(q:ℝ)^(d-2))*((q:ℝ)^2*Real.exp (P/10000)) :=
      mul_le_mul hN hsmall hn.le (by positivity)
    _ = (4*Real.exp (P/10000))*(q:ℝ)^d := by
      rw [show (q:ℝ)^d=(q:ℝ)^(d-2)*(q:ℝ)^2 by rw [←pow_add];congr 1;omega]
      ring

end

open Filter ParameterHierarchy
open scoped Topology

lemma dimensionalScale_oriented_lower {q d : ℕ} {σ n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hnhi : n≤10*Real.exp (((d:ℝ)+1)*σ/2)) :
    Real.exp (((d:ℝ)-1)*σ/2)/10≤dimensionalScale q d n := by
  unfold dimensionalScale
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (Real.exp (((d:ℝ)-1)*σ/2)/10)*(10*Real.exp (((d:ℝ)+1)*σ/2)) :=
      mul_le_mul_of_nonneg_left hnhi (by positivity)
    _ = Real.exp ((d:ℝ)*σ) := by
      rw [show (Real.exp (((d:ℝ)-1)*σ/2)/10)*(10*Real.exp (((d:ℝ)+1)*σ/2))=
        Real.exp (((d:ℝ)-1)*σ/2)*Real.exp (((d:ℝ)+1)*σ/2) by ring,←Real.exp_add]
      congr 1
      ring
    _ = (q:ℝ)^d := by rw [hq,←Real.exp_nat_mul]

lemma dimensional_strong_scale {q d : ℕ} {σ n P : ℝ} (hd : 2≤d)
    (hσ : 100≤σ) (hq : (q:ℝ)=Real.exp σ) (hn : 0<n)
    (hnhi : n≤10*Real.exp (((d:ℝ)+1)*σ/2)) (hP : 1≤P) (hPhi : P≤σ/10) :
    2+dimensionalScale q d n*Real.exp (-3*P)≤dimensionalScale q d n*Real.exp (-P) := by
  let B := dimensionalScale q d n
  have hBlo := dimensionalScale_oriented_lower hq hn hnhi
  have hdR : (2:ℝ)≤d := by exact_mod_cast hd
  have hlarge : 4≤B*Real.exp (-P) := by
    have he := Real.add_one_le_exp (((d:ℝ)-1)*σ/2-P)
    have hh : Real.exp (((d:ℝ)-1)*σ/2-P)/10≤B*Real.exp (-P) := by
      calc
        _ = (Real.exp (((d:ℝ)-1)*σ/2)/10)*Real.exp (-P) := by rw [Real.exp_sub,Real.exp_neg];ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hBlo (Real.exp_nonneg _)
    nlinarith
  have hE : Real.exp (-2*P)≤1/2 := by
    have he : (2:ℝ)≤Real.exp (2*P) := by linarith [Real.add_one_le_exp (2*P)]
    rw [show -2*P=-(2*P) by ring,Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he)
  have hB : 0≤B := by unfold B dimensionalScale;positivity
  have hterm : B*Real.exp (-3*P)≤(B*Real.exp (-P))/2 := by
    calc
      _ = (B*Real.exp (-P))*Real.exp (-2*P) := by rw [mul_assoc,←Real.exp_add];congr 2;ring
      _ ≤ (B*Real.exp (-P))*(1/2) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  linarith

theorem eventually_low_geometric_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q d m : ℕ) (n D : ℝ) (R : ℕ),
      2≤d → d≤4 → (q:ℝ)=Real.exp σ → 0<n →
      n≤10*Real.exp (((d:ℝ)+1)*σ/2) →
      n≤(q:ℝ)^2*Real.exp (P η σ D R/10000) →
      (m:ℝ)≤Real.exp (3*σ) → Range η σ D R →
      let B := dimensionalScale q d n
      let p := momentOrder σ (P η σ D R)
      let a := dyadFactor m (P η σ D R/100)
      10000≤L η σ D ∧
      40*B*Real.exp (L η σ D/100)+2*((p+1:ℝ)*
        lowMomentBudget (pencilAlphabet q d) (a*B^2) (a*B) B (Real.exp (σ/5))
          (L η σ D) p R (pencilAlphabet q (d-1)) (pencilAlphabet q (d-2)))≤
        B*Real.exp (P η σ D R/5) ∧
      (pencilAlphabet q d:ℝ)+(a*B^2)/(1/(100*(p:ℝ)))^200≤B^2*Real.exp (P η σ D R/10) ∧
      (p:ℝ)^2≤Real.exp (P η σ D R/10) ∧
      2+B*Real.exp (-3*P η σ D R)≤B*Real.exp (-P η σ D R) := by
  let c : ℝ := 8*2^(200:ℕ)
  have hcost := eventually_low_poly_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hpairs := eventually_high_pair_cost hη hη' 10002 c (by norm_num) (by positivity)
  have hhier := eventually_hierarchy hη hη' 0 (1/10) 10000 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),hcost,hpairs,hhier] with σ hσ hc hp hh
  intro q d m n D R hd hdhi hq hn hnor hlow hm hr
  have hσ1 : 1≤σ := by linarith
  obtain ⟨hD,hR,hpow,hLlo,hLhi,hPlo,hPhi⟩ := finite_bounds hη hη' hσ1 hr
  have ht := hh D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
  have hL : 10000≤L η σ D := ht.1
  have hPσ : P η σ D R≤σ/10 := by simpa only [div_eq_mul_inv,one_mul,mul_comm (10⁻¹:ℝ)] using ht.2.1
  have hL0 : 0<L η σ D := by linarith
  have hR1 : 1≤(R:ℝ) := hpow.trans hr.rlo
  have hP1 : 1≤P η σ D R := by unfold P; nlinarith
  let B := dimensionalScale q d n
  let p := momentOrder σ (P η σ D R)
  let a := dyadFactor m (P η σ D R/100)
  obtain ⟨_,hpos,_,_,hps⟩ := momentOrder_bounds hσ1 hP1
  have hrat := dimensional_budget_ratios hd hdhi (by linarith) hq hn hnor
  have hB : 0<B := lt_of_lt_of_le zero_lt_one hrat.1
  have hB1 : 1≤B := hrat.1
  have ha : 0≤a := by dsimp [a,dyadFactor];positivity
  have has : a ≤ c*σ*Real.exp (P η σ D R/50) := dyadFactor_exp_bound hσ1 hm
  have hs := low_one_anchor_ratio hd hdhi (by linarith) hq hn hlow
  have hc' := hc D R p a ((pencilAlphabet q (d-1):ℝ)/B) hr
    (Nat.cast_nonneg _) hps ha has hs
  have hp' := hp D R p a hr (Nat.cast_nonneg _) hps ha has
  have hbudget := lowMomentBudget_le_poly (pencilAlphabet q d) a
    ((pencilAlphabet q (d-1):ℝ)/B) B (Real.exp (σ/5)) (L η σ D) p R
    (pencilAlphabet q (d-1)) (pencilAlphabet q (d-2)) hB1 (Real.exp_pos _) ha hL0.le
    hrat.2.1 hrat.2.2.1 hrat.2.2.2 (le_refl _)
  have hPL : (R:ℝ)*L η σ D=P η σ D R := by unfold P;ring
  rw [hPL] at hbudget
  have hsingleton : 40*Real.exp (L η σ D/100)≤Real.exp (P η σ D R/50) := by
    have h40 : (40:ℝ)≤Real.exp (L η σ D/100) := by linarith [Real.add_one_le_exp (L η σ D/100)]
    calc
      _ ≤ Real.exp (L η σ D/100)*Real.exp (L η σ D/100) := mul_le_mul_of_nonneg_right h40 (Real.exp_nonneg _)
      _ = Real.exp (L η σ D/50) := by rw [←Real.exp_add];congr 1;ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold P;nlinarith)
  refine ⟨hL,?_,?_,hp'.2,dimensional_strong_scale hd hσ hq hn hnor hP1 hPσ⟩
  · calc
      _ ≤ B*Real.exp (P η σ D R/50)+2*((p+1:ℝ)*(B*lowBudgetPoly a
          ((pencilAlphabet q (d-1):ℝ)/B) p (P η σ D R))) := by
        apply add_le_add
        · nlinarith only [mul_le_mul_of_nonneg_left hsingleton hB.le]
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (by positivity)) (by norm_num)
      _ = B*(Real.exp (P η σ D R/50)+2*(p+1)*lowBudgetPoly a
          ((pencilAlphabet q (d-1):ℝ)/B) p (P η σ D R)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' hB.le
  · have htpos : 0<1/(100*(p:ℝ)) := by positivity
    have hQ : (pencilAlphabet q d:ℝ)≤400*B^2 := (div_le_iff₀ (sq_pos_of_pos hB)).mp hrat.2.2.2
    calc
      _ = (pencilAlphabet q d:ℝ)+B^2*(a*(100*(p:ℝ))^200) := by rw [div_pow,one_pow];field_simp;ring
      _ ≤ 400*B^2+B^2*(a*(100*(p:ℝ))^200) := add_le_add hQ (le_refl _)
      _ = B^2*(400+a*(100*(p:ℝ))^200) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp'.1 (sq_nonneg _)

end SharpRamseyFive.ScoreGeometry

end

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma plane_one_anchor (hdim : finrank K V=3)
    (F : Finset (ℙ K (Dual K V))) (l : RadialLine x) :
    (Finset.univ.filter fun H:F => l∈pencilLines x F H).card≤1 := by
  simpa only [hdim,Nat.reduceSub,Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,zero_add]
    using one_anchor_count x F l

lemma plane_pencil_disjoint (hdim : finrank K V=3)
    (F : Finset (ℙ K (Dual K V))) {H H' : F} (hne : H≠H') :
    Disjoint (pencilLines x F H) (pencilLines x F H') := by
  apply Finset.disjoint_left.mpr
  intro l hl hl'
  have he := Finset.card_le_one.mp (plane_one_anchor x hdim F l) H
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩) H'
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl'⟩)
  exact hne he

lemma plane_overlap_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {H H' : F} (hne : H≠H') :
    mass (radialWeight x X δ) (pencilLines x F H∩pencilLines x F H')=0 := by
  rw [Finset.disjoint_iff_inter_eq_empty.mp (plane_pencil_disjoint x hdim F hne)]
  exact Finset.sum_empty

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end

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

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_low_original_tail {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (d : ℕ) (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=d+1 → 2≤d → d≤4 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ)≤10*Real.exp (((d:ℝ)+1)*σ/2) →
      (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=d) S C ((L₀:ℝ)/100) →
      (∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
          u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
            (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
          (scale (K:=K) d S.card)^2*Real.exp (P η σ D R/50)) →
      (∀H:F,∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
          (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
          scale (K:=K) d S.card*Real.exp (P η σ D R/50)) →
      (∀H:F,
        ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(momentOrder σ (P η σ D R):ℝ)) ≤ mass
          (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
          scale (K:=K) d S.card*Real.exp (-3*P η σ D R)) →
      scale (K:=K) d S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have hh := eventually_low_geometric_budget hη hη'
  have ho := eventually_moment_orders hη hη'
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  filter_upwards [eventually_ge_atTop (100:ℝ),hh,ho,hm] with σ hσ hh ho hm
  intro d D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hd hd' hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hSlow hn hf hF hx hpairs hrows hdegree ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hcard : ((outsideAt x S (C a∪C b)).card:ℝ)≤Real.exp (3*σ) := by
    have hsub : (outsideAt x S (C a∪C b)).card≤S.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        have hy' : y.val∈S\(C a∪C b) := by simpa [outsideAt] using hy
        exact (Finset.mem_sdiff.mp hy').1
      · intro y hy z hz he
        exact Subtype.ext he
    have hdR : (d:ℝ)≤4 := by exact_mod_cast hd'
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith [Real.add_one_le_exp (σ/2)]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr hsub
      _ ≤ 10*Real.exp (((d:ℝ)+1)*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := by
        apply mul_le_mul he (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hbudget := hh (Nat.card K) d (outsideAt x S (C a∪C b)).card S.card D R
    hd hd' hq hsn hSn hSlow hcard hr
  obtain ⟨heven,hp,hplo,hphi,hps,hKR,hhpos,hhsize,herr⟩ := ho D R hr
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hP0 : 0<P η σ D R := lt_of_lt_of_le (by norm_num) hmargin.2.1
  have hpP : 1000*Real.log (Nat.card K)≤(momentOrder σ (P η σ D R):ℝ)*((L₀:ℝ)*R) := by
    rw [hq,Real.log_exp,hPL]
    have ht := (div_le_iff₀ hP0).mp hplo
    linarith
  apply low_original_tail x hdim hd S C hS a b c ha hb hc F hF hf hn L₀
    (by simpa only [hL] using hbudget.1) R (momentOrder σ (P η σ D R)) (residualOrder σ)
    hp heven hKR hhpos (hhsize.trans (Nat.div_le_div_right (Nat.sub_le _ _))) herr hx
    (Real.exp (σ/5)) (Real.one_le_exp_iff.mpr (by linarith))
    (by simpa only [hPL] using hpairs) (by simpa only [hPL] using hrows)
    (by simpa only [hPL] using hdegree)
    (by simpa only [hPL,scale,dimensionalScale] using hbudget.2.2.2.2)
    (by simpa only [hPL] using hbudget.2.2.2.1)
    (by simpa only [hPL,scale,dimensionalScale] using hbudget.2.2.1)
    (by simpa only [hL,scale,dimensionalScale,ParameterHierarchy.P] using hbudget.2.1)
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) hpP ht

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneStrongExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma plane_pair_card_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun z : DistinctPairs F => t ≤
      strength (pencilLines x F) (radialWeight x X δ) z).card=0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he := plane_overlap_zero x hdim X δ F z.2.property.symm
  exact (not_le.mpr ht) (he▸(Finset.mem_filter.mp hz).2)

lemma plane_degree_card_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun H':F => H≠H' ∧ t ≤
      mass (radialWeight x X δ) (pencilLines x F H∩pencilLines x F H')).card=0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H' hH'
  obtain ⟨hne,hm⟩ := (Finset.mem_filter.mp hH').2
  rw [plane_overlap_zero x hdim X δ F hne] at hm
  exact (not_le.mpr ht) hm

lemma plane_validation_card_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun z : {z : F×F // z.1≠z.2} => t ≤
      mass (radialWeight x X δ) (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card=0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hm := (Finset.mem_filter.mp hz).2
  rw [plane_overlap_zero x hdim X δ F z.property] at hm
  exact (not_le.mpr ht) hm

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_tails {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ) ≤ 10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=2) S C ((L₀:ℝ)/100) →
      scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let E := {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|}
      μ.real E ≤ Real.exp (-P η σ D R/2) ∧ μ.real E ≤ (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have ht := eventually_validation_original_tail hη hη' Cb hCb
  have ha := eventually_low_original_tail hη hη' Cb hCb
  have ho := eventually_moment_orders hη hη'
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,ha,ho] with σ hσ ht ha ho
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t
    hdim hq hr hL hb₀ hbhi hτ hS hCa hCb hCc hSn hn hf hF hx ht₀
  dsimp only
  have hNor : (S.card:ℝ) ≤ 10*Real.exp (((2:ℝ)+1)*σ/2) := by norm_num;exact hSn
  have hP0 : 0 ≤ P η σ D R := by unfold P; rw [←hL];exact mul_nonneg L₀.coe_nonneg (Nat.cast_nonneg R)
  have hSlow : (S.card:ℝ) ≤ (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) := by
    have he : (10:ℝ) ≤ Real.exp (σ/2) := by linarith [Real.add_one_le_exp (σ/2)]
    calc
      _ ≤ 10*Real.exp (3*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (3*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = (Nat.card K:ℝ)^2 := by rw [hq,←Real.exp_add,←Real.exp_nat_mul];norm_num;ring
      _ ≤ _ := le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp_iff.mpr (by positivity))
  constructor
  · apply ht 2 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
      hCa hCb hCc hNor hn hf hF hx _ ht₀
    intro u hu hu2
    rw [plane_validation_card_zero x hdim _ _ F hu,Nat.cast_zero,zero_mul]
    positivity
  · apply ha 2 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
      hCa hCb hCc hNor hSlow hn hf hF hx _ _ _ ht₀
    · intro u hu hu2
      change ((Finset.univ.filter fun z : DistinctPairs F => u ≤ strength (pencilLines x F)
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z).card:ℝ)*u^200 ≤ _
      rw [plane_pair_card_zero x hdim _ _ F hu,Nat.cast_zero,zero_mul]
      positivity
    · intro H u hu hu2
      rw [plane_degree_card_zero x hdim _ _ F H hu,Nat.cast_zero,zero_mul]
      unfold scale;positivity
    · intro H
      have hp : 0 < (momentOrder σ (P η σ D R):ℝ) := Nat.cast_pos.mpr (ho D R hr).2.1
      rw [plane_degree_card_zero x hdim _ _ F H (by positivity),Nat.cast_zero]
      unfold scale;positivity

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
namespace SharpRamseyFive.ScoreScalars

lemma regular_training_payment {L P : ℝ} (hL : 100000000≤L) (hLP : 100*L≤P) :
    200000*Real.exp (-2*(L/100))+Real.exp (-P/2)≤Real.exp (-L/1000) := by
  have h₁ := exp_sub_le_scaled (a:=L/1000) (b:=2*(L/100)) (C:=400000) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤400000),hL])
  have h₂ := exp_sub_le_scaled (a:=L/1000) (b:=P/2) (C:=2) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤2),hL,hLP])
  simp only [neg_div,neg_mul] at *
  linarith only [h₁,h₂]

lemma ambient_two_payment {σ : ℝ} (hσ : 100≤σ) :
    2*Real.exp (2*σ)*(Real.exp σ)^(-(50:ℝ))≤1/2 := by
  rw [←Real.exp_mul, mul_assoc,←Real.exp_add]
  have h := exp_sub_le_scaled (a:=0) (b:=48*σ) (C:=4) (by norm_num)
    (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤4),hσ])
  simp only [neg_zero,Real.exp_zero] at h
  have he : 2*σ+σ*(-50)=-(48*σ) := by ring
  rw [he]
  linarith only [h]

end SharpRamseyFive.ScoreScalars

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_integrals_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (U S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
      (ia ib ic : ℙ K V→J),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → S.Nonempty →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (S.card:ℝ)≤10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let O := fun x => C (ia x)∪C (ib x)
      let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
      let t := scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
      (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
      (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤(S.card:ℝ) := by
  have ht := eventually_two_score_tails hη hη' Cb hCb
  have hm := eventually_score_margins hη hη' Cb hCb
  have hl := eventually_hierarchy hη hη' Cb 1 100000000 hCb (by norm_num)
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hm,hl] with σ hσ ht hm hl
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ _ J _ U S C ia ib ic hdim hq hr hL hb₀ hbhi hτ
    hS hC hCS hCc hSn hn hf
  dsimp only
  let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
  let O := fun x => C (ia x)∪C (ib x)
  let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let t := scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
  let bad := irregular (d:=2) S C ((L₀:ℝ)/100)
  let E : ℙ K V→Set (Fin R→S→ℕ) := fun x => {ω | Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\exceptional S C) (ctr x) ω|}
  have hn1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hlarge : 100000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b₀ τ hr hbhi hτ).1
  have hLP : 100*(L₀:ℝ)≤P η σ D R := by rw [hL];exact (hm D b₀ τ R hr hb₀ hbhi hτ).2.2.2.1
  have hbad := irregular_card_bound (d:=2) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have htail (x : ℙ K V) (hx : x∉bad) :
      μ.real (E x)≤Real.exp (-P η σ D R/2) ∧ μ.real (E x)≤(Nat.card K:ℝ)^(-(50:ℝ)) := by
    apply ht D b₀ τ R L₀ K V x S C (ia x) (ib x) (ic x) (pencil x\exceptional S C) t
      hdim hq hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) hSn hn (hf x) _ hx (le_refl _)
    intro H hH
    have hh := Finset.mem_sdiff.mp hH
    exact ⟨(Finset.mem_filter.mp hh.1).2,hh.2⟩
  constructor
  · have hh := integral_filter_card_le μ S bad E (Real.exp_nonneg _)
      (fun x hx => (htail x (Finset.mem_sdiff.mp hx).2).1)
    change (∫ω,((S.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=(bad.card:ℝ)+S.card*Real.exp (-P η σ D R/2)) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      congr 2
      ext x
      simp only [Finset.mem_filter]
    calc
      _ ≤ 200000*(S.card:ℝ)*Real.exp (-2*((L₀:ℝ)/100))+S.card*Real.exp (-P η σ D R/2) :=
        add_le_add hbad le_rfl
      _ = (S.card:ℝ)*(200000*Real.exp (-2*((L₀:ℝ)/100))+Real.exp (-P η σ D R/2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ScoreScalars.regular_training_payment hlarge hLP) (Nat.cast_nonneg _)
  · have hh := integral_filter_card_le μ U bad E (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun x hx => (htail x (Finset.mem_sdiff.mp hx).2).2)
    change (∫ω,((U.filter fun x => ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=(bad.card:ℝ)+U.card*(Nat.card K:ℝ)^(-(50:ℝ))) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      congr 2
      ext x
      simp only [Finset.mem_filter]
    have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
    have hq2 : (2:ℝ)≤Nat.card K := by rw [hq];linarith only [Real.add_one_le_exp σ,hσ]
    have hU : (U.card:ℝ)≤2*Real.exp (2*σ) := by
      have hp := Finset.card_le_univ U
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim] at hp
      norm_num [Finset.sum_range_succ] at hp
      have hh : (U.card:ℝ)≤1+Nat.card K+(Nat.card K:ℝ)^2 := by exact_mod_cast hp
      have hqpow : (Nat.card K:ℝ)^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul];norm_num
      rw [←hqpow]
      nlinarith only [hh,hq2]
    have hpay := ScoreScalars.ambient_two_payment hσ
    have hu : (U.card:ℝ)*(Nat.card K:ℝ)^(-(50:ℝ))≤1/2 := by
      rw [hq]
      exact (mul_le_mul_of_nonneg_right hU (by positivity)).trans hpay
    have hrpay := ScoreScalars.exp_sub_le_scaled (a:=0) (b:=2*((L₀:ℝ)/100)) (C:=400000) (by norm_num)
      (by linarith only [Real.log_le_self (by norm_num : (0:ℝ)≤400000),hlarge])
    simp only [neg_zero,Real.exp_zero] at hrpay
    rw [show -(2*((L₀:ℝ)/100))=(-2)*((L₀:ℝ)/100) by ring] at hrpay
    have hb : (bad.card:ℝ)≤(S.card:ℝ)/2 := by
      apply hbad.trans
      nlinarith only [mul_le_mul_of_nonneg_right hrpay (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)]
    linarith only [hb,hu,hn1]

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals_oai
