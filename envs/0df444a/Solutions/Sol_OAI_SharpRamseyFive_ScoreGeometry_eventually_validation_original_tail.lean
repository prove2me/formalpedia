-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:44:15.671757+00:00
-- url     : https://prove2.me/submissions/81d65446-fc99-4b43-8dc0-e12bfe6d1272

import Mathlib
import Definitions.Def_OAIQ060R004

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

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PositiveTailMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.TailMoment
open scoped BigOperators Classical

theorem positive_tail_moment {I : Type*} [Fintype I] (f : I → ℝ)
    (hf0 : ∀ i,0 < f i) (hf2 : ∀ i,f i ≤ 2) (A : ℝ) (hA : 0 ≤ A)
    (K R : ℕ) (hR : K+1 ≤ R)
    (htail : ∀ a : ℝ,0 < a → a ≤ 2 →
      ((Finset.univ.filter fun i => a ≤ f i).card:ℝ)*a^K ≤ A) :
    ∑ i,f i^R ≤ 2*A*2^R := by
  have hnear (i : I) : ∃ n : ℕ,(1/2:ℝ)^(n+1) < f i/2 ∧ f i/2 ≤ (1/2:ℝ)^n :=
    exists_nat_pow_near_of_lt_one (div_pos (hf0 i) (by norm_num)) (by linarith [hf2 i])
      (by norm_num) (by norm_num)
  let index : I → ℕ := fun i => (hnear i).choose
  have hind (i : I) := (hnear i).choose_spec
  let N := Finset.univ.sup index+1
  have hidx (i : I) (_ : i ∈ Finset.univ) : index i ∈ Finset.range N := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  rw [←Finset.sum_fiberwise_of_maps_to hidx (fun i => f i^R)]
  have hlevel (n : ℕ) :
      (∑ i ∈ Finset.univ.filter fun i => index i=n,f i^R) ≤ A*2^R*(1/2:ℝ)^n := by
    let E := Finset.univ.filter fun i => index i=n
    let a : ℝ := (1/2:ℝ)^n
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsub : E ⊆ Finset.univ.filter fun i => a ≤ f i := by
      intro i hi
      have he := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
      have hlo := (hind i).1
      change (1/2:ℝ)^(index i+1) < f i/2 at hlo
      rw [he,pow_succ] at hlo
      dsimp [a]
      linarith
    have hc : (E.card:ℝ)*a^K ≤ A :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
        (pow_nonneg ha.le _)).trans (htail a ha (ha1.trans (by norm_num)))
    calc
      _ ≤ ∑ i ∈ E,(2*a)^R := Finset.sum_le_sum fun i hi => by
        have he := (Finset.mem_filter.mp hi).2
        have hup := (hind i).2
        change f i/2 ≤ (1/2:ℝ)^(index i) at hup
        rw [he] at hup
        exact pow_le_pow_left₀ (hf0 i).le (by dsimp [a]; linarith) R
      _ = (E.card:ℝ)*2^R*a^R := by rw [Finset.sum_const,nsmul_eq_mul,mul_pow]; ring
      _ ≤ (E.card:ℝ)*2^R*a^(K+1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one ha.le ha1 hR) (by positivity)
      _ = ((E.card:ℝ)*a^K)*(2^R*a) := by rw [pow_succ]; ring
      _ ≤ A*(2^R*a) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.range N,A*2^R*(1/2:ℝ)^n := Finset.sum_le_sum fun n _ => hlevel n
    _ = A*2^R*∑ n ∈ Finset.range N,(1/2:ℝ)^n := (Finset.mul_sum ..).symm
    _ ≤ A*2^R*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (by positivity)
    _ = _ := by ring

theorem tail_moment {I : Type*} [Fintype I] (f : I → ℝ)
    (hf0 : ∀ i,0 ≤ f i) (hf2 : ∀ i,f i ≤ 2) (A : ℝ) (hA : 0 ≤ A)
    (K R : ℕ) (hR : K+1 ≤ R)
    (htail : ∀ a : ℝ,0 < a → a ≤ 2 →
      ((Finset.univ.filter fun i => a ≤ f i).card:ℝ)*a^K ≤ A) :
    ∑ i,f i^R ≤ 2*A*2^R := by
  let S := Finset.univ.filter fun i => 0 < f i
  have hs : (∑ i,f i^R) = ∑ i ∈ S,f i^R := by
    apply (Finset.sum_subset (Finset.subset_univ _) _).symm
    intro i _ hi
    have hzero : f i = 0 := by
      have := not_lt.mp (show ¬0 < f i by simpa [S] using hi)
      linarith [hf0 i]
    simp [hzero,show R ≠ 0 by omega]
  rw [hs]
  rw [Finset.sum_subtype S (p := fun i => 0 < f i) (by intro i; simp [S])]
  apply positive_tail_moment (fun i : {i : I // 0 < f i} => f i.val)
    (fun i => i.property) (fun i => hf2 i.val) A hA K R hR
  intro a ha ha2
  have hc : (Finset.univ.filter fun i : {i : I // 0 < f i} => a ≤ f i.val).card ≤
      (Finset.univ.filter fun i => a ≤ f i).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.val)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg ha.le _)).trans
    (htail a ha ha2)

end SharpRamseyFive.TailMoment

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_SumDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ValidationBounds
open scoped BigOperators Classical

lemma sum_diagonal {H : Type*} [Fintype H] (f : H → H → ℝ) :
    (∑ h,∑ k,f h k) = (∑ h,f h h) +
      ∑ z : {z : H × H // z.1 ≠ z.2},f z.val.1 z.val.2 := by
  classical
  rw [← Fintype.sum_prod_type']
  have he : (∑ z : H × H,f z.1 z.2) =
      (∑ z : H × H with z.1 = z.2,f z.1 z.2) +
      ∑ z : H × H with z.1 ≠ z.2,f z.1 z.2 := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : H × H => z.1=z.2) _).symm
  rw [he]
  congr 1
  · rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp
  · rw [Finset.sum_subtype (Finset.univ.filter fun z : H × H => z.1 ≠ z.2)
      (p := fun z => z.1 ≠ z.2) (by intro z; simp)]

theorem overlap_power_sum {H : Type*} [Fintype H] (θ : H → H → ℝ)
    (hθ0 : ∀ h k,0 ≤ θ h k) (hθ2 : ∀ h k,θ h k ≤ 2)
    (A C : ℝ) (hA : 0 ≤ A) (hcard : (Fintype.card H:ℝ) ≤ C)
    (K R : ℕ) (hR : K+1 ≤ R)
    (htail : ∀ a : ℝ,0 < a → a ≤ 2 →
      ((Finset.univ.filter fun z : {z : H × H // z.1 ≠ z.2} => a ≤ θ z.val.1 z.val.2).card:ℝ)*a^K ≤ A) :
    (∑ h,∑ k,θ h k^R) ≤ (C+2*A)*2^R := by
  rw [sum_diagonal]
  have hd : (∑ h,θ h h^R) ≤ C*2^R := by
    calc
      _ ≤ ∑ _h : H,(2:ℝ)^R := Finset.sum_le_sum fun h _ =>
        pow_le_pow_left₀ (hθ0 h h) (hθ2 h h) R
      _ = Fintype.card H*2^R := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have ho := TailMoment.tail_moment (fun z : {z : H × H // z.1 ≠ z.2} => θ z.val.1 z.val.2)
    (fun z => hθ0 _ _) (fun z => hθ2 _ _) A hA K R hR htail
  exact (add_le_add hd ho).trans_eq (by ring)

end SharpRamseyFive.ValidationBounds

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

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

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
open Module ProjectiveIncidence CellVariance
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

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ValidationBudgetWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ValidationBounds
open scoped BigOperators Classical
lemma validation_budget_wide {B P L : ℝ} {R : ℕ}
    (hP : 100000 ≤ P) (hR : (R:ℝ) ≤ P/100000)
    (hLR : 100*L ≤ P)
    (D S : ℝ) (hD0 : 0 ≤ D) (hD : D ≤ 100*B*Real.exp (L/100))
    (hS : S ≤ (400*B^2+2*(B^2*Real.exp (P/50)))*2^R) :
    D^2+S ≤ B^2*Real.exp (3*P/100) := by
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hpow : (2:ℝ)^R ≤ Real.exp (P/100000) := by
    rw [show (2:ℝ)^R = Real.exp ((R:ℝ)*Real.log 2) by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]]
    apply Real.exp_le_exp.mpr
    calc
      (R:ℝ)*Real.log 2 ≤ (R:ℝ)*1 := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ P/100000 := by simpa using hR
  have hE : 1 ≤ Real.exp (P/50) := Real.one_le_exp (by linarith)
  have hS' : S ≤ 402*B^2*Real.exp (P/50+P/100000) := by
    calc
      S ≤ (400*B^2+2*(B^2*Real.exp (P/50)))*2^R := hS
      _ ≤ (402*B^2*Real.exp (P/50))*Real.exp (P/100000) := by
        apply mul_le_mul _ hpow (by positivity) (by positivity)
        nlinarith [sq_nonneg B,mul_le_mul_of_nonneg_left hE (sq_nonneg B)]
      _ = _ := by rw [Real.exp_add]; ring
  have hD' : D^2 ≤ 10000*B^2*Real.exp (P/5000) := by
    calc
      _ ≤ (100*B*Real.exp (L/100))^2 := pow_le_pow_left₀ hD0 hD 2
      _ = 10000*B^2*Real.exp (2*(L/100)) := by
        rw [show Real.exp (2*(L/100)) = Real.exp (L/100)^2 by
          simpa using Real.exp_nat_mul (L/100) 2]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hD'' : D^2 ≤ 10000*B^2*Real.exp (P/50+P/100000) := hD'.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity))
  have hcoef : (10402:ℝ) ≤ Real.exp (3*P/100-(P/50+P/100000)) := by
    have ht : (100:ℝ) ≤ 3*P/100-(P/50+P/100000) := by linarith
    have he' : (10402:ℝ) ≤ Real.exp (100:ℝ) := by
      have he2 := Real.add_one_le_exp (25:ℝ)
      have he26 : (26:ℝ) ≤ Real.exp 25 := by linarith
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26) he26 4
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp
      exact (by norm_num : (10402:ℝ)≤456976).trans hp
    exact he'.trans (Real.exp_le_exp.mpr ht)
  calc
    D^2+S ≤ 10402*B^2*Real.exp (P/50+P/100000) := by linarith [hD'',hS']
    _ ≤ Real.exp (3*P/100-(P/50+P/100000))*B^2*Real.exp (P/50+P/100000) := by
      gcongr
    _ = _ := by rw [mul_assoc,mul_left_comm,← Real.exp_add]; congr 2; ring

lemma final_validation_budget_wide {B P L N D S : ℝ} {R : ℕ}
    (hP : 100000≤P) (hL : 1≤L) (hPR : P=L*(R:ℝ))
    (hR : (R:ℝ)≤P/100000) (hlog : (R:ℝ)*Real.log L≤P/100)
    (hN : N≤400*B^2) (hN0 : 0≤N) (hDS : D^2+S≤B^2*Real.exp (3*P/100)) :
    N*(2*Real.exp (-L*(3/4)))^R+
      (2*L^2*Real.exp (-L*(3/4)))^R*(D^2+S) ≤ B^2*Real.exp (-3*P/5) := by
  have hL0 : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : Real.log 2≤1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have he1 : (2*Real.exp (-L*(3/4)))^R=
      Real.exp ((R:ℝ)*Real.log 2-3*P/4) := by
    rw [hPR]
    have hx : (R:ℝ)*Real.log 2-3*(L*(R:ℝ))/4=(R:ℝ)*(Real.log 2+(-L*(3/4))) := by ring
    rw [hx,Real.exp_nat_mul,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have he2 : (2*L^2*Real.exp (-L*(3/4)))^R=
      Real.exp ((R:ℝ)*Real.log 2+2*((R:ℝ)*Real.log L)-3*P/4) := by
    rw [hPR]
    have hx : (R:ℝ)*Real.log 2+2*((R:ℝ)*Real.log L)-3*(L*(R:ℝ))/4=
        (R:ℝ)*(Real.log 2+((2:ℕ):ℝ)*Real.log L+(-L*(3/4))) := by ring
    rw [hx,Real.exp_nat_mul,Real.exp_add,Real.exp_add,Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_log hL0]
  have hh : (R:ℝ)*Real.log 2≤P/100000 := by
    exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg R)).trans (by simpa using hR)
  have hp1 : (2*Real.exp (-L*(3/4)))^R≤Real.exp (-74*P/100) := by
    rw [he1]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp2 : (2*L^2*Real.exp (-L*(3/4)))^R≤Real.exp (-72*P/100) := by
    rw [he2]
    exact Real.exp_le_exp.mpr (by linarith)
  have hc : (400:ℝ)≤Real.exp (P/20) := by
    have he := Real.add_one_le_exp (P/20)
    linarith
  have hd : N*(2*Real.exp (-L*(3/4)))^R≤B^2*Real.exp (-69*P/100) := by
    calc
      _ ≤ (400*B^2)*Real.exp (-74*P/100) :=
        mul_le_mul hN hp1 (by positivity) (hN0.trans hN)
      _ ≤ (Real.exp (P/20)*B^2)*Real.exp (-74*P/100) := by gcongr
      _ = B^2*(Real.exp (P/20)*Real.exp (-74*P/100)) := by ring
      _ = B^2*Real.exp (P/20+(-74*P/100)) := by rw [Real.exp_add]
      _ = _ := by congr 2; ring
  have ho : (2*L^2*Real.exp (-L*(3/4)))^R*(D^2+S)≤B^2*Real.exp (-69*P/100) := by
    calc
      _ ≤ (2*L^2*Real.exp (-L*(3/4)))^R*(B^2*Real.exp (3*P/100)) :=
        mul_le_mul_of_nonneg_left hDS (by positivity)
      _ ≤ Real.exp (-72*P/100)*(B^2*Real.exp (3*P/100)) :=
        mul_le_mul_of_nonneg_right hp2 (by positivity)
      _ = B^2*(Real.exp (-72*P/100)*Real.exp (3*P/100)) := by ring
      _ = B^2*Real.exp (-72*P/100+3*P/100) := by rw [Real.exp_add]
      _ = _ := by congr 2; ring
  have htwo : (2:ℝ)≤Real.exp (9*P/100) := by
    have he := Real.add_one_le_exp (9*P/100)
    linarith
  calc
    _ ≤ 2*(B^2*Real.exp (-69*P/100)) := by linarith only [hd,ho]
    _ ≤ Real.exp (9*P/100)*(B^2*Real.exp (-69*P/100)) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = B^2*(Real.exp (9*P/100)*Real.exp (-69*P/100)) := by ring
    _ = B^2*Real.exp (9*P/100+(-69*P/100)) := by rw [Real.exp_add]
    _ = _ := by congr 2; ring

end SharpRamseyFive.ValidationBounds

end

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
lemma measurableSet_emptyEvent (s : Finset ι) : MeasurableSet (emptyEvent s) := by
  exact MeasurableSet.pi (s.finite_toSet.countable) (fun _ _ => measurableSet_singleton 0)

omit [DecidableEq ι] in
lemma measure_emptyEvent (rate : ι → ℝ≥0) (s : Finset ι) :
    batchMeasure rate (emptyEvent s) = ENNReal.ofReal (Real.exp (-mass rate s)) := by
  rw [batchMeasure, emptyEvent, Measure.pi_pi_finset]
  simp_rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl
omit [DecidableEq ι] in

lemma integral_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    ∫ ω, emptyIndicator s ω ∂batchMeasure rate = Real.exp (-mass rate s) := by
  simp only [emptyIndicator]
  rw [integral_indicator_const _ (measurableSet_emptyEvent s),
    Measure.real, measure_emptyEvent, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp
omit [DecidableEq ι] in

lemma integrable_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    Integrable (emptyIndicator s) (batchMeasure rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_emptyEvent s)

omit [Fintype ι] in
lemma emptyIndicator_mul (s t : Finset ι) (ω : ι → ℕ) :
    emptyIndicator s ω * emptyIndicator t ω = emptyIndicator (s ∪ t) ω := by
  have hu : emptyEvent (s ∪ t) = emptyEvent s ∩ emptyEvent t := by
    ext x
    simp [emptyEvent, Set.mem_pi, or_imp, forall_and]
  rw [emptyIndicator, emptyIndicator, emptyIndicator, hu]
  by_cases hs : ω ∈ emptyEvent s <;> by_cases ht : ω ∈ emptyEvent t <;>
    simp [hs, ht]

omit [Fintype ι] in
lemma mass_union_inter (rate : ι → ℝ≥0) (s t : Finset ι) :
    mass rate (s ∪ t) + mass rate (s ∩ t) = mass rate s + mass rate t := by
  exact Finset.sum_union_inter

omit [DecidableEq ι] in

lemma integrable_centeredFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    Integrable (centeredFactor s b) (batchMeasure rate) :=
  (integrable_emptyIndicator rate s).sub (integrable_const b)
omit [DecidableEq ι] in

lemma integral_centeredFactor (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    ∫ ω, centeredFactor s b ω ∂batchMeasure rate = Real.exp (-mass rate s) - b := by
  simp only [centeredFactor]
  rw [integral_sub (integrable_emptyIndicator rate s)
    (integrable_const b), integral_emptyIndicator]
  simp

lemma integral_centeredFactor_mul (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) :
    (∫ ω, centeredFactor s b ω * centeredFactor t b ω ∂batchMeasure rate) =
      (Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b) +
      Real.exp (-(mass rate s + mass rate t)) *
        (Real.exp (mass rate (s ∩ t)) - 1) := by
  have he : (fun ω => centeredFactor s b ω * centeredFactor t b ω) =
      fun ω => emptyIndicator (s ∪ t) ω - b * emptyIndicator s ω -
        b * emptyIndicator t ω + b ^ 2 := by
    funext ω
    rw [centeredFactor, centeredFactor]
    have := emptyIndicator_mul s t ω
    nlinarith [this]
  rw [he]
  have hs := integrable_emptyIndicator rate s
  have ht := integrable_emptyIndicator rate t
  have hu := integrable_emptyIndicator rate (s ∪ t)
  have h1 := integral_sub hu (hs.const_mul b)
  have h2 := integral_sub (hu.sub (hs.const_mul b)) (ht.const_mul b)
  have h3 := integral_add ((hu.sub (hs.const_mul b)).sub (ht.const_mul b))
    (integrable_const (b ^ 2))
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h3, h2, h1]
  simp only [integral_const_mul, integral_emptyIndicator, integral_const,
    probReal_univ, one_smul]
  have hmass := mass_union_inter rate s t
  have hu : Real.exp (-mass rate (s ∪ t)) =
      Real.exp (-(mass rate s + mass rate t)) * Real.exp (mass rate (s ∩ t)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hp : Real.exp (-mass rate s) * Real.exp (-mass rate t) =
      Real.exp (-(mass rate s + mass rate t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hu]
  nlinarith [hp]

omit [Fintype ι] [DecidableEq ι] in
lemma emptyIndicator_nonneg (s : Finset ι) (ω : ι → ℕ) : 0 ≤ emptyIndicator s ω := by
  unfold emptyIndicator
  apply Set.indicator_nonneg
  intro _ _
  norm_num

omit [Fintype ι] [DecidableEq ι] in
lemma abs_centeredFactor_le_one (s : Finset ι) (b : ℝ) (hb : b ∈ Set.Icc 0 1)
    (ω : ι → ℕ) : |centeredFactor s b ω| ≤ 1 := by
  unfold centeredFactor emptyIndicator
  by_cases h : ω ∈ emptyEvent s <;> simp [h, abs_le] <;> constructor <;> linarith [hb.1, hb.2]

omit [DecidableEq ι] in

lemma integral_abs_centeredFactor_le (rate : ι → ℝ≥0) (s : Finset ι) (b : ℝ) :
    (∫ ω, |centeredFactor s b ω| ∂batchMeasure rate) ≤ Real.exp (-mass rate s) + |b| := by
  calc
    _ ≤ ∫ ω, emptyIndicator s ω + |b| ∂batchMeasure rate := by
      apply integral_mono (integrable_centeredFactor rate s b).abs
        ((integrable_emptyIndicator rate s).add (integrable_const |b|))
      intro ω
      dsimp [centeredFactor]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (emptyIndicator_nonneg s ω)])
    _ = _ := by
      rw [integral_add (integrable_emptyIndicator rate s) (integrable_const |b|),
        integral_emptyIndicator]
      simp

lemma abs_exp_neg_sub_exp_neg_le {a b c : ℝ} (ha : c ≤ a) (hb : c ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-c) * |a - b| := by
  have ordered : ∀ {a b : ℝ}, c ≤ a → a ≤ b →
      Real.exp (-a) - Real.exp (-b) ≤ Real.exp (-c) * (b - a) := by
    intro a b hca hab
    have he := Real.add_one_le_exp (a - b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have hprod : Real.exp (-a) * Real.exp (a - b) = Real.exp (-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hprod] at hm
    have hec : Real.exp (-a) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (neg_le_neg hca)
    have hd := mul_le_mul_of_nonneg_right hec (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using ordered ha hab
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg hba))),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    simpa only [neg_sub] using ordered hb hba

omit [DecidableEq ι] in

lemma abs_integral_centeredFactor_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hmass : mass rate s = L * lam)
    (hlam : c ≤ lam) (hbase : c ≤ base) :
    |∫ ω, centeredFactor s (Real.exp (-L * base)) ω ∂batchMeasure rate| ≤
      L * Real.exp (-L * c) * |lam - base| := by
  rw [integral_centeredFactor, hmass]
  have he := abs_exp_neg_sub_exp_neg_le
    (mul_le_mul_of_nonneg_left hlam hL) (mul_le_mul_of_nonneg_left hbase hL)
  simpa only [neg_mul, mul_neg, ← mul_sub, abs_mul, abs_of_nonneg hL, mul_comm,
    mul_left_comm, mul_assoc] using he

omit [DecidableEq ι] in

lemma integral_abs_centeredFactor_exp_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hmass : mass rate s = L * lam)
    (hlam : c ≤ lam) (hbase : c ≤ base) :
    (∫ ω, |centeredFactor s (Real.exp (-L * base)) ω| ∂batchMeasure rate) ≤
      2 * Real.exp (-L * c) := by
  have h1 := integral_abs_centeredFactor_le rate s (Real.exp (-L * base))
  rw [hmass, abs_of_pos (Real.exp_pos _)] at h1
  have h2 : Real.exp (-(L * lam)) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : Real.exp (-L * base) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

lemma integrable_centeredFactor_mul (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) :
    Integrable (fun ω => centeredFactor s b ω * centeredFactor t b ω) (batchMeasure rate) := by
  have he : (fun ω => centeredFactor s b ω * centeredFactor t b ω) =
      fun ω => emptyIndicator (s ∪ t) ω - b * emptyIndicator s ω -
        b * emptyIndicator t ω + b ^ 2 := by
    funext ω
    rw [centeredFactor, centeredFactor]
    nlinarith [emptyIndicator_mul s t ω]
  rw [he]
  exact (((integrable_emptyIndicator rate (s ∪ t)).sub
    ((integrable_emptyIndicator rate s).const_mul b)).sub
    ((integrable_emptyIndicator rate t).const_mul b)).add (integrable_const (b^2))

omit [Fintype ι] [DecidableEq ι] in
lemma mass_nonneg (rate : ι → ℝ≥0) (s : Finset ι) : 0 ≤ mass rate s := by
  exact Finset.sum_nonneg (fun i _ => (rate i).coe_nonneg)

omit [Fintype ι] [DecidableEq ι] in
lemma mass_mono (rate : ι → ℝ≥0) {s t : Finset ι} (hst : s ⊆ t) :
    mass rate s ≤ mass rate t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (rate i).coe_nonneg)

lemma one_sub_exp_neg_le (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

omit [Fintype ι] in

lemma covariance_le (rate : ι → ℝ≥0) (s t : Finset ι) :
    Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1) ≤
    mass rate (s ∩ t) * Real.exp (-mass rate (s ∪ t)) := by
  have hu := mass_union_inter rate s t
  have he : Real.exp (-(mass rate s + mass rate t)) =
      Real.exp (-mass rate (s ∪ t)) * Real.exp (-mass rate (s ∩ t)) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  rw [he]
  have hh : Real.exp (-mass rate (s ∩ t)) * Real.exp (mass rate (s ∩ t)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hb := mul_le_mul_of_nonneg_left (one_sub_exp_neg_le (mass rate (s ∩ t)))
    (Real.exp_pos (-mass rate (s ∪ t))).le
  calc
    _ = Real.exp (-mass rate (s ∪ t)) * (1 - Real.exp (-mass rate (s ∩ t))) := by
      rw [mul_assoc, mul_sub, hh, mul_one]
    _ ≤ _ := by simpa only [mul_comm] using hb
omit [Fintype ι] in

lemma covariance_nonneg (rate : ι → ℝ≥0) (s t : Finset ι) :
    0 ≤ Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1) := by
  apply mul_nonneg (Real.exp_pos _).le
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mass_nonneg rate _))

lemma abs_integral_centeredFactor_mul_le_mass (rate : ι → ℝ≥0)
    (s t : Finset ι) (b : ℝ) :
    |∫ ω, centeredFactor s b ω * centeredFactor t b ω ∂batchMeasure rate| ≤
      |Real.exp (-mass rate s) - b| * |Real.exp (-mass rate t) - b| +
      mass rate (s ∩ t) * Real.exp (-mass rate (s ∪ t)) := by
  rw [integral_centeredFactor_mul]
  calc
    _ ≤ |(Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b)| +
        |Real.exp (-(mass rate s + mass rate t)) *
          (Real.exp (mass rate (s ∩ t)) - 1)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (covariance_nonneg rate s t)]
      exact add_le_add le_rfl (covariance_le rate s t)

lemma abs_integral_centeredFactor_mul_exp_le (rate : ι → ℝ≥0)
    (s t : Finset ι) {L lam₁ lam₂ base c θ : ℝ}
    (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hs : mass rate s = L * lam₁) (ht : mass rate t = L * lam₂)
    (hi : mass rate (s ∩ t) = L * θ)
    (h₁ : c ≤ lam₁) (h₂ : c ≤ lam₂) (hbase : c ≤ base) :
    |∫ ω, centeredFactor s (Real.exp (-L * base)) ω *
      centeredFactor t (Real.exp (-L * base)) ω ∂batchMeasure rate| ≤
        L ^ 2 * Real.exp (-L * c) * (|lam₁ - base| * |lam₂ - base| + θ) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hi0 := mass_nonneg rate (s ∩ t)
  have hθ : 0 ≤ θ := by rw [hi] at hi0; nlinarith
  have hu : L * c ≤ mass rate (s ∪ t) := by
    calc
      _ ≤ L * lam₁ := mul_le_mul_of_nonneg_left h₁ hL0
      _ = mass rate s := hs.symm
      _ ≤ mass rate (s ∪ t) := mass_mono rate Finset.subset_union_left
  have huse : Real.exp (-mass rate (s ∪ t)) ≤ Real.exp (-L * c) :=
    Real.exp_le_exp.mpr (by linarith)
  have hepos := Real.exp_pos (-L * c)
  have hele : Real.exp (-L * c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e₁ := abs_integral_centeredFactor_le rate s hL0 hs h₁ hbase
  have e₂ := abs_integral_centeredFactor_le rate t hL0 ht h₂ hbase
  rw [integral_centeredFactor] at e₁ e₂
  have hmul := mul_le_mul e₁ e₂ (abs_nonneg _)
    (mul_nonneg (mul_nonneg hL0 hepos.le) (abs_nonneg _))
  have hab := mul_nonneg (abs_nonneg (lam₁ - base)) (abs_nonneg (lam₂ - base))
  have hpow : Real.exp (-L * c) ^ 2 ≤ Real.exp (-L * c) := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (sq_nonneg L) hab)
  have hcov := mul_le_mul_of_nonneg_left huse hi0
  rw [hi] at hcov
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hcov' := mul_le_mul_of_nonneg_right hLsq (mul_nonneg hθ hepos.le)
  have hfinal := abs_integral_centeredFactor_mul_le_mass rate s t (Real.exp (-L * base))
  nlinarith

lemma integrable_scoreTerm_mul (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    Integrable (fun ω => scoreTerm s b ownS ω * scoreTerm t b ownT ω)
      (scheduleMeasure rate R) := by
  simp only [scoreTerm, ← Finset.prod_mul_distrib]
  apply Integrable.fintype_prod (f := fun r ω => (if ownS r then centeredFactor s b ω else 0) * (if ownT r then centeredFactor t b ω else 0))
  intro r
  cases hs : ownS r <;> cases ht : ownT r <;>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero]
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_const 0
  · exact integrable_centeredFactor_mul rate s t b

lemma integral_scoreTerm_mul (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    (∫ ω, scoreTerm s b ownS ω * scoreTerm t b ownT ω ∂scheduleMeasure rate R) =
      ∏ r, if ownS r && ownT r then pairMean rate s t b else 0 := by
  simp only [scoreTerm, ← Finset.prod_mul_distrib, scheduleMeasure]
  rw [integral_fintype_prod_eq_prod (f := fun r ω => (if ownS r then centeredFactor s b ω else 0) * (if ownT r then centeredFactor t b ω else 0))]
  congr 1
  funext r
  cases hs : ownS r <;> cases ht : ownT r <;>
    simp [integral_centeredFactor_mul, pairMean]

lemma abs_integral_scoreTerm_mul_le (rate : ι → ℝ≥0) {R : ℕ} (s t : Finset ι) (b : ℝ)
    (ownS ownT : Fin R → Bool) :
    |∫ ω, scoreTerm s b ownS ω * scoreTerm t b ownT ω ∂scheduleMeasure rate R| ≤
      |pairMean rate s t b| ^ R := by
  rw [integral_scoreTerm_mul, Finset.abs_prod]
  calc
    _ ≤ ∏ _ : Fin R, |pairMean rate s t b| := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro r _
      split_ifs <;> simp
    _ = _ := by simp

variable {κ : Type*}

lemma integral_typicalScore_sq (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) :
    (∫ ω, (typicalScore H directions b own ω)^2 ∂scheduleMeasure rate R) =
      ∑ h ∈ H, ∑ k ∈ H,
        ∏ r, if own h r && own k r then pairMean rate (directions h) (directions k) b else 0 := by
  simp only [typicalScore, pow_two]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum H (fun h _ =>
    integrable_finsetSum H (fun k _ =>
      integrable_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k)))]
  apply Finset.sum_congr rfl
  intro h _
  rw [integral_finsetSum H (fun k _ =>
      integrable_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k))]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_scoreTerm_mul rate (directions h) (directions k) b (own h) (own k)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_IntegralTypicalScoreSq
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
lemma integral_typicalScore_sq_le (rate : ι → ℝ≥0) {R : ℕ} (H : Finset κ)
    (directions : κ → Finset ι) (b : ℝ) (own : κ → Fin R → Bool) :
    (∫ ω, (typicalScore H directions b own ω)^2 ∂scheduleMeasure rate R) ≤
      ∑ h ∈ H, ∑ k ∈ H, |pairMean rate (directions h) (directions k) b|^R := by
  rw [integral_typicalScore_sq]
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro k _
  rw [← integral_scoreTerm_mul]
  exact (le_abs_self _).trans
    (abs_integral_scoreTerm_mul_le rate (directions h) (directions k) b (own h) (own k))

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

omit [DecidableEq ι] [DecidableEq D] [Fintype H] in
theorem original_uniform_score_moment (p : ι→Prop) [DecidablePred p]
    (e : {i // ¬p i}≃D) (rate : ℝ≥0) {R : ℕ}
    (F : Finset H) (lines : H→Finset D) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (own : (Fin R→{i // p i}→ℕ)→H→Fin R→Bool) (k : ℕ) (B : ℝ)
    (hB : ∀ u,(∫ v,(typicalScore F lines b (own u) v)^k
      ∂scheduleMeasure (fun _ : D => rate) R)≤B) :
    (∫ ω,(typicalScore F lines b (own (fun r i => ω r i))
      (fun r d => ω r (e.symm d).val))^k ∂scheduleMeasure (fun _ : ι => rate) R)≤B := by
  apply integral_split_schedule_le (fun _ : ι => rate) p
    (fun u v => (typicalScore F lines b (own u) (fun r d => v r (e.symm d)))^k)
    ((F.card:ℝ)^k) B
  · intro u v
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_typicalScore_le_card F lines hb (own u) _) k
  · intro u
    rw [integral_schedule_reindex e (fun _ : D => rate)
      (fun v => (typicalScore F lines b (own u) v)^k)]
    exact hB u

end SharpRamseyFive.PoissonScore

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

namespace SharpRamseyFive.ValidationMoment
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators NNReal Classical

private lemma add_power_bound {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (R : ℕ) :
    (a+b)^R≤2^R*(a^R+b^R) := by
  apply (add_pow_le ha hb R).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.sub_le R 1)) (by positivity)

theorem finite_second_sum {H : Type*} [Fintype H] [DecidableEq H]
    (M θ : H → H → ℝ) (d : H → ℝ) (a c : ℝ) (_ha : 0≤a) (hc : 0 ≤ c)
    (hd : ∀ h,0≤d h ∧ d h≤1) (hθ : ∀ h k,0≤θ h k)
    (hdiag : ∀ h,|M h h|≤a) (hoff : ∀ h k,h≠k → |M h k| ≤ c*(d h*d k+θ h k))
    (R : ℕ) (hR : 2≤R) :
    (∑ h,∑ k,|M h k|^R) ≤ (Fintype.card H:ℝ)*a^R+
      (2*c)^R*((∑ h,(d h)^2)^2+∑ h,∑ k∈Finset.univ.erase h,(θ h k)^R) := by
  have hp (h k : H) (hne : h≠k) : |M h k|^R ≤
      (2*c)^R*((d h)^2*(d k)^2+(θ h k)^R) := by
    calc
      _ ≤ (c*(d h*d k+θ h k))^R := pow_le_pow_left₀ (abs_nonneg _) (hoff h k hne) R
      _ = c^R*(d h*d k+θ h k)^R := mul_pow _ _ _
      _ ≤ c^R*(2^R*((d h*d k)^R+(θ h k)^R)) :=
        mul_le_mul_of_nonneg_left (add_power_bound (mul_nonneg (hd h).1 (hd k).1) (hθ h k) R)
          (pow_nonneg hc R)
      _ = (2*c)^R*((d h)^R*(d k)^R+(θ h k)^R) := by rw [mul_pow,mul_pow];ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add <;> try rfl
        exact mul_le_mul (pow_le_pow_of_le_one (hd h).1 (hd h).2 hR)
          (pow_le_pow_of_le_one (hd k).1 (hd k).2 hR) (pow_nonneg (hd k).1 R) (sq_nonneg _)
  have hs : (∑ h,∑ k,|M h k|^R)=
      (∑ h,|M h h|^R)+(∑ h,∑ k∈Finset.univ.erase h,|M h k|^R) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    exact (Finset.add_sum_erase Finset.univ (fun k => |M h k|^R) (Finset.mem_univ h)).symm
  rw [hs]
  have hdg : (∑ h,|M h h|^R)≤(Fintype.card H:ℝ)*a^R := by
    calc
      _ ≤ ∑ _h : H,a^R := Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (abs_nonneg _) (hdiag h) R
      _ = _ := by simp
  apply add_le_add hdg
  calc
    _ ≤ ∑ h,∑ k∈Finset.univ.erase h,(2*c)^R*((d h)^2*(d k)^2+(θ h k)^R) := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro k hk
      exact hp h k (Ne.symm (Finset.mem_erase.mp hk).1)
    _ = (2*c)^R*((∑ h,∑ k∈Finset.univ.erase h,(d h)^2*(d k)^2)+
        ∑ h,∑ k∈Finset.univ.erase h,(θ h k)^R) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add <;> try rfl
      calc
        _ ≤ ∑ h,∑ k,(d h)^2*(d k)^2 := by
          apply Finset.sum_le_sum
          intro h _
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun k _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = _ := by rw [pow_two,Finset.sum_mul];simp only [Finset.mul_sum]

variable {D H : Type*} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

omit [Fintype D] [DecidableEq D] in
lemma mass_scale (a : D → ℝ≥0) (L : ℝ≥0) (S : Finset D) :
    mass (fun d => L*a d) S=(L:ℝ)*mass a S := by
  simp only [mass,NNReal.coe_mul,Finset.mul_sum]

lemma diagonal_one_batch (a : D → ℝ≥0) (L : ℝ≥0) (S : Finset D)
    (base c : ℝ) (hc : 0 ≤ c) (hm : c≤ mass a S) (hb : c≤base) :
    |pairMean (fun d => L*a d) S S (Real.exp (-(L:ℝ)*base))| ≤
      2*Real.exp (-(L:ℝ)*c) := by
  rw [pairMean, ←integral_centeredFactor_mul]
  apply (abs_integral_le_integral_abs).trans
  apply le_trans _ (integral_abs_centeredFactor_exp_le _ S L.coe_nonneg (mass_scale a L S) hm hb)
  apply integral_mono (integrable_centeredFactor_mul _ S S _).abs (integrable_centeredFactor _ S _).abs
  intro ω
  dsimp only
  rw [abs_mul]
  have hle := abs_centeredFactor_le_one S (Real.exp (-(L:ℝ)*base))
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) (hc.trans hb))⟩ ω
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (abs_nonneg (centeredFactor S (Real.exp (-(L:ℝ)*base)) ω))

theorem poisson_validation_second (a : D → ℝ≥0) (lines : H → Finset D)
    (L : ℝ≥0) (hL : 1≤(L:ℝ)) (base c : ℝ) (hc : 0 ≤ c) (hb : c≤base)
    (hm : ∀ h,c≤ mass a (lines h)) (hd : ∀ h,|mass a (lines h)-base|≤1)
    (R : ℕ) (hR : 2≤R) (own : H → Fin R → Bool) :
    (∫ ω,(typicalScore Finset.univ lines (Real.exp (-(L:ℝ)*base)) own ω)^2
      ∂scheduleMeasure (fun d => L*a d) R) ≤
      (Fintype.card H:ℝ)*(2*Real.exp (-(L:ℝ)*c))^R+
      (2*(L:ℝ)^2*Real.exp (-(L:ℝ)*c))^R*
        ((∑ h,|mass a (lines h)-base|^2)^2+
          ∑ h,∑ k∈Finset.univ.erase h,(mass a (lines h ∩ lines k))^R) := by
  apply (integral_typicalScore_sq_le (fun d => L*a d) Finset.univ lines _ own).trans
  have hh := finite_second_sum
    (fun h k => pairMean (fun d => L*a d) (lines h) (lines k) (Real.exp (-(L:ℝ)*base)))
    (fun h k => mass a (lines h ∩ lines k)) (fun h => |mass a (lines h)-base|)
    (2*Real.exp (-(L:ℝ)*c)) ((L:ℝ)^2*Real.exp (-(L:ℝ)*c)) (by positivity) (by positivity)
    (fun h => ⟨abs_nonneg _,hd h⟩) (fun _ _ => mass_nonneg _ _)
    (fun h => diagonal_one_batch a L (lines h) base c hc (hm h) hb) (by
      intro h k _
      rw [pairMean, ←integral_centeredFactor_mul]
      exact abs_integral_centeredFactor_mul_exp_le _ _ _ hL hc
        (mass_scale a L (lines h)) (mass_scale a L (lines k))
        (mass_scale a L (lines h ∩ lines k)) (hm h) (hm k) hb) R hR
  simpa only [mul_assoc] using hh

end SharpRamseyFive.ValidationMoment

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

omit [Fintype H] in
lemma integral_original_score_pow (label : ι→D) (rate : ι→ℝ≥0)
    {R : ℕ} (s : Finset H) (lines : H→Finset D) (b : ℝ)
    (own : H→Fin R→Bool) (p : ℕ) :
    (∫ ω,(typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω)^p
      ∂scheduleMeasure rate R) =
    ∫ ω,(typicalScore s lines b own ω)^p ∂scheduleMeasure (aggregateRate label rate) R := by
  simp_rw [←typicalScore_aggregate label s lines b own]
  exact (measurePreserving_schedule_aggregate label rate R).hasLaw.integral_comp
    (measurable_of_countable (fun ω : Fin R→D→ℕ => (typicalScore s lines b own ω)^p)).aestronglyMeasurable

end SharpRamseyFive.PoissonScore

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

variable [Finite K]

omit [Fintype (RadialLine x)] in
lemma pencil_size (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) :
    F.card ≤ ∑ i ∈ Finset.range (finrank K V-1), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : F → {b : ℙ K (Module.Dual K V) // Incident x b} := fun H => ⟨H.val,hF H.val H.property⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // Incident x b} => b.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [card_hyperplanes_through_point, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

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

end SharpRamseyFive.ScoreGeometry

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

theorem original_radial_moment (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) {R : ℕ}
    (b : ℝ) (own : F→Fin R→Bool) (p : ℕ) :
    (∫ ω,(typicalScore Finset.univ
      (fun H : F => Finset.univ.filter fun y : X => Incident y.val.val H.val) b own ω)^p
      ∂scheduleMeasure (fun _ : X => L*δ) R) =
    ∫ ω,(typicalScore Finset.univ (pencilLines x F) b own ω)^p
      ∂scheduleMeasure (fun l => L*radialWeight x X δ l) R := by
  have h := integral_original_score_pow (radialLabel x X) (fun _ => L*δ)
    Finset.univ (pencilLines x F) b own p
  simp_rw [radialLabel_in_pencil x X F hF,aggregateRate_radialLabel] at h
  exact h

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
open Module ProjectiveIncidence CellVariance
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

open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma typical_variance_component {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C) {ξ : ℝ}
    (hx : x∉irregular (d:=d) S C ξ) (j : Option J) :
    (∑ H : F,(deviation S C j H.val)^2) ≤ scale (K:=K) d S.card*Real.exp ξ := by
  have hr : weightOnPencil (clippedWeight S C (some j)) x ≤ scale (K:=K) d S.card*Real.exp ξ := by
    by_contra hn
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,some j,lt_of_not_ge hn⟩)
  have he : (∑ H : F,(deviation S C j H.val)^2)=
      ∑ H∈F,incidenceEntry x H*clippedWeight S C (some j) H := by
    rw [Finset.sum_coe_sort F (fun H => (deviation S C j H)^2)]
    apply Finset.sum_congr rfl
    intro H hH
    have hd := typical_deviation S C (hF H hH).2 j
    have ht : threshold j ≤ 1 := by cases j <;> norm_num [threshold]
    have hs : (deviation S C j H)^2 ≤ 1 := by
      have ha := abs_nonneg (deviation S C j H)
      have hb := hd.trans ht
      nlinarith [sq_abs (deviation S C j H)]
    simp only [incidenceEntry,ite_eq_left (hF H hH).1,clippedWeight,min_eq_right hs,one_mul]
  rw [he]
  apply le_trans _ hr
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro H _ _
  have hw := (clippedWeight_bounds S C (some j) H).1
  by_cases h : Incident x H <;> simp [incidenceEntry,h,hw]

lemma Q_le_two_pow (q k : ℕ) (hq : 2≤q) : (Q q k:ℝ) ≤ 2*(q:ℝ)^k-1 := by
  induction k with
  | zero => norm_num [Q]
  | succ k ih =>
    have he : (Q q (k+1):ℝ)=(Q q k:ℝ)+(q:ℝ)^(k+1) := by
      unfold Q
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_pow]
    rw [he,pow_succ]
    have hq' : (2:ℝ)≤q := by exact_mod_cast hq
    have hp := pow_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) k
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]

omit [Fintype (ℙ K V)] in
lemma typical_pencil_card {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H) : (F.card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-1) := by
  have hf : F ⊆ Finset.univ.filter (Incident x) := fun H hH =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF H hH⟩
  have he : (Finset.univ.filter (Incident x)).card=Q (Nat.card K) (d-1) := by
    rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card,card_hyperplanes_through_point,hdim]
    unfold Q
    congr 1
    congr 1
    omega
  have hc : (F.card:ℝ)≤Q (Nat.card K) (d-1) := by exact_mod_cast (Finset.card_le_card hf).trans_eq he
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  linarith [Q_le_two_pow (Nat.card K) (d-1) hq]

omit [Fintype (ℙ K V)] in
lemma queryLoss_square_sum {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (S O : Finset (ℙ K V)) (hS : S.Nonempty) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(queryLoss S O x H.val)^2) ≤ 2*scale (K:=K) d S.card := by
  have hn0 : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hδ : 0≤(Nat.card K:ℝ)/S.card := by positivity
  have hc := typical_pencil_card hdim hd x F hF
  have he : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  calc
    _ ≤ ∑ H : F,((Nat.card K:ℝ)/S.card)^2 := by
      apply Finset.sum_le_sum
      intro H _
      exact pow_le_pow_left₀ (queryLoss_bounds S O x H.val).1 (queryLoss_bounds S O x H.val).2 2
    _ = (F.card:ℝ)*((Nat.card K:ℝ)/S.card)^2 := by simp
    _ ≤ (2*(Nat.card K:ℝ)^(d-1))*((Nat.card K:ℝ)/S.card)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 2*scale (K:=K) d S.card*((Nat.card K:ℝ)/S.card) := by
      unfold scale
      rw [←he]
      ring
    _ ≤ 2*scale (K:=K) d S.card := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by norm_num) (scale_nonneg _ _ hn0.le))

lemma four_sq (a b c d : ℝ) : (a-b-c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b),sq_nonneg (c+d),sq_nonneg ((a-b)+(c-d))]

theorem typical_mass_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      40*scale (K:=K) d S.card*Real.exp ξ := by
  have hv (j : Option J) := typical_variance_component S C x F hF hx j
  have hl := queryLoss_square_sum hdim hd S (C a∪C b) hS x F (fun H hH => (hF H hH).1) hn
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  have he : 1≤Real.exp ξ := Real.one_le_exp_iff.mpr hξ
  have hs : (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      8*((∑ H : F,(deviation S C none H.val)^2)+
        (∑ H : F,(deviation S C (some a) H.val)^2)+
        (∑ H : F,(deviation S C (some b) H.val)^2)+
        (∑ H : F,(deviation S C (some c) H.val)^2))+
      2*∑ H : F,(queryLoss S (C a∪C b) x H.val)^2 := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro H _
    rw [outsideMass_deviation S C hS a b c ha hb hc x H.val]
    have h4 := four_sq (deviation S C none H.val) (deviation S C (some a) H.val)
      (deviation S C (some b) H.val) (deviation S C (some c) H.val)
    nlinarith [sq_nonneg (deviation S C none H.val-deviation S C (some a) H.val-
      deviation S C (some b) H.val+deviation S C (some c) H.val+
      queryLoss S (C a∪C b) x H.val)]
  have hb' := mul_le_mul_of_nonneg_left he hB
  nlinarith only [hs,hv none,hv (some a),hv (some b),hv (some c),hl,hb',hB]

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

theorem actual_radial_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤1) :
    (∑ H : F,|mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H)-(1-ownFraction S (C a) (C b))|^2)≤
        40*scale (K:=K) d S.card*Real.exp ξ := by
  simp_rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1),sq_abs]
  exact typical_mass_variance hdim hd S C hS a b c ha hb hc x F hF hξ hx hn

theorem actual_validation_second {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (L : ℝ≥0) (hL : 1≤(L:ℝ)) (R : ℕ) (hR : 2≤R) (own : F→Fin R→Bool) :
    (∫ ω,(typicalScore Finset.univ
      (fun H : F => Finset.univ.filter fun y : outsideAt x S (C a∪C b) => Incident y.val.val H.val)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) own ω)^2
      ∂scheduleMeasure (fun _ : outsideAt x S (C a∪C b) => L*pointStrength S) R) ≤
      (F.card:ℝ)*(2*Real.exp (-(L:ℝ)*(3/4)))^R+
      (2*(L:ℝ)^2*Real.exp (-(L:ℝ)*(3/4)))^R*
        ((40*scale (K:=K) d S.card*Real.exp ξ)^2+
          ∑ H : F,∑ H'∈Finset.univ.erase H,
            (mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
              (pencilLines x F H∩pencilLines x F H'))^R) := by
  rw [original_radial_moment x _ L (pointStrength S) F (fun H hH => (hF H hH).1)]
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hv := actual_radial_variance x hdim hd S C hS a b c ha hb hc F hF hξ hx
    (hn.trans (by norm_num))
  have h := ValidationMoment.poisson_validation_second
    (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F)
    L hL (1-ownFraction S (C a) (C b)) (3/4) (by norm_num) (by linarith)
    (fun H => (hm H).1) (fun H => (hm H).2.1.trans (by norm_num)) R hR own
  apply h.trans
  simp only [Fintype.card_coe]
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ (le_refl _)
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hv 2

end SharpRamseyFive.ScoreGeometry

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

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

variable [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_original_validation {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (L : ℝ≥0) (hL : 1≤(L:ℝ)) (R : ℕ) (hR : 2≤R) :
    (∫ ω,(modifiedPointScore x S (C a∪C b) F
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω)^2
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R) ≤
      (F.card:ℝ)*(2*Real.exp (-(L:ℝ)*(3/4)))^R+
      (2*(L:ℝ)^2*Real.exp (-(L:ℝ)*(3/4)))^R*
        ((40*scale (K:=K) d S.card*Real.exp ξ)^2+
          ∑ H : F,∑ H'∈Finset.univ.erase H,
            (mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
              (pencilLines x F H∩pencilLines x F H'))^R) := by
  have hbase : Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have hb0 : 0≤1-ownFraction S (C a) (C b) := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) hb0
  apply original_uniform_score_moment (ownQuery x S (C a∪C b))
    (outsideEquiv x S (C a∪C b)) (L*pointStrength S) Finset.univ _ hbase
    (ownBitsMinus x S (C a∪C b) F) 2
  intro u
  exact actual_validation_second x hdim hd S C hS a b c ha hb hc F hF hf hn hξ hx L hL R hR _

end

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

end SharpRamseyFive.PoissonScore

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

omit [Finite K] [FiniteDimensional K V] [Fintype (RadialLine x)] in
theorem unsampled_moment_tail (S O : Finset (ℙ K V)) (rate : S→ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} {b t B : ℝ}
    (hb : b∈Set.Icc 0 1) {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,(modifiedPointScore x S O F b ω)^p ∂scheduleMeasure rate R)≤B) :
    (scheduleMeasure rate R).real {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|}≤B/t^p := by
  have h := weighted_moment_tail (scheduleMeasure rate R) (modifiedPointScore x S O F b)
    (fun _ => (1:ℝ)) (abs_modifiedPointScore x S O F hb)
    (fun _ => ⟨by norm_num,le_refl _⟩) hp ht (by simpa only [one_mul] using hB)
  apply (measureReal_mono (μ:=scheduleMeasure rate R) ?_ (measure_ne_top _ _)).trans h
  intro ω hω
  refine ⟨rfl,?_⟩
  rw [modifiedPointScore_eq x S O F b ω hω.1]
  exact hω.2

end SharpRamseyFive.ScoreGeometry

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

end

open Filter ParameterHierarchy
open scoped Topology

end SharpRamseyFive.ScoreGeometry

end

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

lemma validation_tail_ratio {B κ P : ℝ} (hB : 0<B)
    (hκ : κ+Real.log 10≤P/20) :
    (B^2*Real.exp (-3*P/5))/(B*Real.exp (-κ)/10)^2≤Real.exp (-P/2) := by
  have he : -3*P/5=-(3/10:ℝ)*((2:ℝ)*P) := by ring
  have hr := moment_tail_ratio (κ:=κ) (α:=3/10) (P:=P) hB 2
  norm_num only [Nat.cast_ofNat] at hr
  rw [←he] at hr
  rw [hr]
  apply Real.exp_le_exp.mpr
  linarith only [hκ]

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ValidationOriginalTailWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem validation_original_tail_wide {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100)
    (L : ℝ≥0) (R : ℕ) (hR : 201≤R)
    (hP : 100000≤(L:ℝ)*R) (hL : 1≤(L:ℝ))
    (hRsmall : (R:ℝ)≤((L:ℝ)*R)/100000)
    (hLR : 100*(L:ℝ)≤(L:ℝ)*R)
    (hlog : (R:ℝ)*Real.log (L:ℝ)≤((L:ℝ)*R)/100)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100))
    (hcard : (F.card:ℝ)≤400*(scale (K:=K) d S.card)^2)
    (htail : ∀ u : ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z : {z : F×F // z.1≠z.2} =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*u^200 ≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    {κ t : ℝ} (hκ : κ+Real.log 10≤((L:ℝ)*R)/20)
    (ht : scale (K:=K) d S.card*Real.exp (-κ)/10≤t) :
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
        (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
      Real.exp (-((L:ℝ)*R)/2) := by
  let B : ℝ := scale (K:=K) d S.card
  let θ := fun H H' : F => mass
    (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H∩pencilLines x F H')
  have hB : 0<B := by
    dsimp [B,scale]
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hsn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hξ : 0≤(L:ℝ)/100 := by positivity
  have ht0 : 0<B*Real.exp (-κ)/10 := by positivity
  have hb0 : Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have : 0≤1-ownFraction S (C a) (C b) := by linarith only [hf]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) this
  have hθ0 : ∀H H',0≤θ H H' := fun _ _ => mass_nonneg _ _
  have hθ2 : ∀H H',θ H H'≤2 := by
    intro H H'
    have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
    have hsub : θ H H' ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
        (fun _ _ _ => NNReal.coe_nonneg _)
    exact hsub.trans (by linarith only [(hm H).2.2])
  have hov := ValidationBounds.overlap_power_sum θ hθ0 hθ2
    (B^2*Real.exp (((L:ℝ)*R)/50)) (400*B^2) (by positivity)
    (by simpa only [Fintype.card_coe] using hcard) 200 R hR (by
      intro u hu hu2
      convert! htail u hu hu2 using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rfl)
  have hs : (∑H:F,∑H'∈Finset.univ.erase H,θ H H'^R)≤∑H:F,∑H':F,θ H H'^R := by
    apply Finset.sum_le_sum
    intro H _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun H' _ _ => pow_nonneg (hθ0 H H') R)
  have hDS := ValidationBounds.validation_budget_wide hP hRsmall hLR
    (40*B*Real.exp ((L:ℝ)/100)) _ (by positivity)
    (by nlinarith only [mul_nonneg hB.le (Real.exp_pos ((L:ℝ)/100)).le]) (hs.trans hov)
  have hv := actual_original_validation x hdim hd S C hS a b c ha hb hc F hF hf hn hξ hx
    L hL R (by omega)
  have hbudget := ValidationBounds.final_validation_budget_wide hP hL rfl hRsmall hlog
    hcard (Nat.cast_nonneg F.card) hDS
  have hm : (∫ω,(modifiedPointScore x S (C a∪C b) F
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω)^2
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤B^2*Real.exp (-3*((L:ℝ)*R)/5) :=
    hv.trans hbudget
  have hprob := unsampled_moment_tail x S (C a∪C b) (fun _ : S => L*pointStrength S)
    F hb0 (show Even 2 by decide) ht0 hm
  have herr := ScoreScalars.validation_tail_ratio hB hκ
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans herr)
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

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

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_validation_original_tail_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
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
      (Nat.card K:ℝ)/S.card≤1/100 → ownFraction S (C a) (C b)≤2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=d) S C ((L₀:ℝ)/100) →
      (∀u:ℝ,0<u → u≤2 →
        ((Finset.univ.filter fun z:{z : F × F // z.1≠z.2} =>
          u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
            (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*u^200≤
          (scale (K:=K) d S.card)^2*Real.exp (P η σ D R/50)) →
      scale (K:=K) d S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10≤t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        Real.exp (-P η σ D R/2) := by
  have hm := ParameterHierarchy.eventually_score_margins hη hη' Cb hCb
  have ho := eventually_moment_orders hη hη'
  filter_upwards [eventually_ge_atTop (20:ℝ),hm,ho] with σ hσ hm ho
  intro d D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t hdim hd hd' hq hr hL hb₀ hbhi hτ hS
    ha hb hc hSn hn hf hF hx hpairs ht
  have hsn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hrat := dimensional_budget_ratios hd hd' hσ hq hsn hSn
  have hcard : (F.card:ℝ)≤400*(scale (K:=K) d S.card)^2 := by
    have hp := pencil_size x F (fun H hH => (hF H hH).1)
    rw [hdim,show d+1-1=d by omega] at hp
    have hc : (F.card:ℝ)≤(pencilAlphabet (Nat.card K) d:ℝ) := by exact_mod_cast hp
    have hB : 0<dimensionalScale (Nat.card K) d S.card := by
      exact lt_of_lt_of_le zero_lt_one hrat.1
    exact hc.trans (by simpa only [scale,dimensionalScale] using
      (div_le_iff₀ (sq_pos_of_pos hB)).mp hrat.2.2.2)
  have hmargin := hm D b₀ τ R hr hb₀ hbhi hτ
  have hPL : (L₀:ℝ)*R=P η σ D R := by rw [hL];rfl
  have hR : 201≤R := by
    have hh := (ho D R hr).2.2.2.2.2.1
    omega
  simpa only [hPL] using validation_original_tail_wide x hdim (by omega) S C hS
    a b c ha hb hc F hF hf hn L₀ R hR (by simpa only [hPL] using hmargin.2.1)
    (by rw [hL]; linarith only [hmargin.1])
    (by simpa only [hPL] using hmargin.2.2.1)
    (by simpa only [hL,ParameterHierarchy.P] using hmargin.2.2.2.1)
    (by simpa only [hL,ParameterHierarchy.P] using hmargin.2.2.2.2.1)
    hx hcard (by simpa only [hPL] using hpairs)
    (by simpa only [hPL] using hmargin.2.2.2.2.2.1) ht

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_validation_original_tail_oai
