-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:06.277226+00:00
-- url     : https://prove2.me/submissions/718cbf1b-e882-4175-8889-32a4fe65d19f

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_low_original_tail
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_score_pair_low_moment

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

lemma finrank_sup [FiniteDimensional K V] {x : ℙ K V}
    {l m : RadialLine x} (hlm : l ≠ m) :
    finrank K (l.val ⊔ m.val : Submodule K V) = 3 := by
  have hn : ¬l.val ≤ m.val := by
    intro h
    apply hlm
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq h
      (l.property.1.trans m.property.1.symm))
  have hi : l.val ⊓ m.val < l.val := lt_of_le_of_ne inf_le_left (by
    intro h
    apply hn
    rw [← h]
    exact inf_le_right)
  have hlt := Submodule.finrank_lt_finrank_of_lt hi
  have hge := Submodule.finrank_mono (le_inf l.property.2 m.property.2)
  have he := Submodule.finrank_sup_add_finrank_inf_eq l.val m.val
  rw [x.finrank_submodule] at hge
  rw [l.property.1] at hlt
  rw [l.property.1, m.property.1] at he
  omega

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
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_OffFiberPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.NondominantOverlap
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

section Finite
variable {I D : Type*} [DecidableEq I] [DecidableEq D]

omit [DecidableEq I] in
lemma card_offFiberPairs (f : I → D) (X : Finset I) :
    (offFiberPairs f X).card = ∑ y ∈ X, (X.filter fun z => f y ≠ f z).card := by
  simp only [offFiberPairs,Finset.card_filter,Finset.sum_product]

omit [DecidableEq I] in
lemma offFiberPairs_many (f : I → D) (X : Finset I)
    (h : ∀ y ∈ X, 2*(X.filter fun z => f y = f z).card ≤ X.card) :
    X.card^2 ≤ 2*(offFiberPairs f X).card := by
  have hrow (y : I) (hy : y ∈ X) : X.card ≤ 2*(X.filter fun z => f y ≠ f z).card := by
    have hp := Finset.card_filter_add_card_filter_not (s := X) (fun z => f y = f z)
    change (X.filter fun z => f y = f z).card + (X.filter fun z => f y ≠ f z).card = X.card at hp
    have hh := h y hy
    omega
  have hs := Finset.sum_le_sum hrow
  simpa only [Finset.sum_const_nat,← Finset.mul_sum,← card_offFiberPairs,pow_two] using hs
end Finite

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V)

lemma planePairs_disjoint (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hA : finrank K A = 3) (hB : finrank K B = 3)
    (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B) (hne : A ≠ B) :
    Disjoint (planePairs x X A) (planePairs x X B) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨y,z⟩ hpa hpb
  obtain ⟨hya,hza⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpa).1
  obtain ⟨hyb,hzb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpb).1
  have hrad := (Finset.mem_filter.mp hpa).2
  let l := RadialLine.through x y.val y.property
  let m := RadialLine.through x z.val z.property
  have hr : finrank K (l.val ⊔ m.val : Submodule K V) = 3 := RadialLine.finrank_sup hrad
  have hlA : l.val ≤ A := (RadialLine.through_le_iff _ _).mpr ⟨hxA,(Finset.mem_filter.mp hya).2⟩
  have hmA : m.val ≤ A := (RadialLine.through_le_iff _ _).mpr ⟨hxA,(Finset.mem_filter.mp hza).2⟩
  have hlB : l.val ≤ B := (RadialLine.through_le_iff _ _).mpr ⟨hxB,(Finset.mem_filter.mp hyb).2⟩
  have hmB : m.val ≤ B := (RadialLine.through_le_iff _ _).mpr ⟨hxB,(Finset.mem_filter.mp hzb).2⟩
  have hEA := Submodule.eq_of_le_of_finrank_eq (sup_le hlA hmA) (hr.trans hA.symm)
  have hEB := Submodule.eq_of_le_of_finrank_eq (sup_le hlB hmB) (hr.trans hB.symm)
  exact hne (hEA.symm.trans hEB)

theorem rich_nondominant_plane_count (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (hxF : ∀ A ∈ F, x.submodule ≤ A) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (onPlane x X A).card)
    (hnd : ∀ A ∈ F, ∀ l : RadialLine x,
      2*((onPlane x X A).filter fun y => y.val.submodule ≤ l.val).card ≤ (onPlane x X A).card) :
    F.card*M^2 ≤ 2*X.card^2 := by
  have hm (A : Submodule K V) (hA : A ∈ F) : M^2 ≤ 2*(planePairs x X A).card := by
    have hh := offFiberPairs_many (fun y : {y : ℙ K V // x ≠ y} => RadialLine.through x y.val y.property)
      (onPlane x X A) (by
        intro y _
        have hr := hnd A hA (RadialLine.through x y.val y.property)
        have he : ((onPlane x X A).filter fun z =>
            RadialLine.through x y.val y.property = RadialLine.through x z.val z.property) =
            ((onPlane x X A).filter fun z => z.val.submodule ≤ (RadialLine.through x y.val y.property).val) := by
          ext z
          simp only [Finset.mem_filter,eq_comm (a := RadialLine.through x y.val y.property),RadialLine.through_eq_iff]
        rwa [he])
    exact (Nat.pow_le_pow_left (hM A hA) 2).trans hh
  have hdisj : (F : Set (Submodule K V)).PairwiseDisjoint (planePairs x X) := by
    intro A hA B hB hne
    exact planePairs_disjoint x X A B (hF A hA) (hF B hB) (hxF A hA) (hxF B hB) hne
  have hsub : F.biUnion (planePairs x X) ⊆ X ×ˢ X := by
    intro p hp
    obtain ⟨A,_,hpA⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hy,hz⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpA).1
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hz).1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj,Finset.card_product] at hc
  have hs := Finset.sum_le_sum hm
  simp only [Finset.sum_const_nat,← Finset.mul_sum] at hs
  exact hs.trans (by nlinarith)

end SharpRamseyFive.NondominantOverlap

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

lemma neighbor_count_by_intersection {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (H : Submodule K V) (E : Finset (Submodule K V))
    (hE : E ⊆ F) (hEL : ∀ A ∈ E, H ⊓ A ∈ L) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
  have hsub : E ⊆ L.biUnion (fun W => F.filter fun A => W ≤ A) := by
    intro A hA
    exact Finset.mem_biUnion.mpr ⟨H ⊓ A,hEL A hA,Finset.mem_filter.mpr ⟨hE hA,inf_le_right⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (F.filter fun A => W ≤ A).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
    simpa only [hL W hW] using card_hyperplanes_containing hdim F hF W
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma neighbor_count_by_contained_witness {d : ℕ} [Finite K] (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (L : Finset (Submodule K V)) (r : ℕ) (hL : ∀ W ∈ L, finrank K W = r)
    (E : Finset (Submodule K V))
    (hE : E ⊆ F) (hEL : ∀ A ∈ E, ∃ W ∈ L, W ≤ A) :
    E.card ≤ L.card*(∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
  have hsub : E ⊆ L.biUnion (fun W => F.filter fun A => W ≤ A) := by
    intro A hA
    obtain ⟨W,hW,hWA⟩ := hEL A hA
    exact Finset.mem_biUnion.mpr ⟨W,hW,Finset.mem_filter.mpr ⟨hE hA,hWA⟩⟩
  have hrow (W : Submodule K V) (hW : W ∈ L) :
      (F.filter fun A => W ≤ A).card ≤ (∑ i ∈ Finset.range (d+1-r), Nat.card K^i) := by
    simpa only [hL W hW] using card_hyperplanes_containing hdim F hF W
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_const_nat] using hh))

lemma rich_radial_count {x : ℙ K V} [Fintype (RadialLine x)]
    (X : Finset {y : ℙ K V // x ≠ y}) (W : Submodule K V) (hx : x.submodule ≤ W)
    (L : Finset (RadialLine x)) (hL : L ⊆ RadialLine.inFlat W) (M : ℕ)
    (hM : ∀ l ∈ L, M ≤ (RadialLine.trainingOnLine X l).card) :
    L.card*M ≤ (X.filter fun y => y.val.submodule ≤ W).card := by
  have h := Finset.sum_le_sum hM
  simp only [Finset.sum_const_nat] at h
  apply h.trans
  rw [← RadialLine.sum_trainingOnLine X W hx]
  exact Finset.sum_le_sum_of_subset hL

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

theorem nondominant_degree_count (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F)
    (hne : ∀ A ∈ E, H ≠ A) (M : ℕ)
    (hM : ∀ A ∈ E, M ≤ (pairPoints x X H A).card)
    (hnd : ∀ A ∈ E, ∀ l : RadialLine x,
      2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X H A).card) :
    E.card*M^2 ≤ 2*(onPlane x X H).card^2*(Nat.card K+1) := by
  let L := E.image fun A => H ⊓ A
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 3 := by
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    exact hyperplane_intersection_rank (d := 4) hdim H A hH (hF A (hE hA)) (hne A hA)
  have hxL (W : Submodule K V) (hW : W ∈ L) : x.submodule ≤ W := by
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    exact le_inf hxH (hxF A (hE hA))
  have hpoints (A : Submodule K V) :
      onPlane x (onPlane x X H) (H ⊓ A) = pairPoints x X H A := by
    ext y
    simp only [onPlane,pairPoints,Finset.mem_filter,le_inf_iff]
    tauto
  have hplanes := rich_nondominant_plane_count x (onPlane x X H) L hL hxL M (by
    intro W hW
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    rw [hpoints]
    exact hM A hA) (by
    intro W hW l
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hW
    rw [hpoints]
    exact hnd A hA l)
  have hpairs := neighbor_count_by_intersection (d := 4) hdim F hF L 3 hL H E hE (by
    intro A hA
    exact Finset.mem_image.mpr ⟨A,hA,rfl⟩)
  have hQ : (∑ i ∈ Finset.range (4+1-3), Nat.card K^i) = Nat.card K+1 := by
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  rw [hQ] at hpairs
  calc
    E.card*M^2 ≤ (L.card*(Nat.card K+1))*M^2 := Nat.mul_le_mul_right _ hpairs
    _ = (L.card*M^2)*(Nat.card K+1) := by ring
    _ ≤ (2*(onPlane x X H).card^2)*(Nat.card K+1) := Nat.mul_le_mul_right _ hplanes

theorem dominant_degree_count [Fintype (RadialLine x)] {d : ℕ}
    (hdim : finrank K V = d+1) (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (H : Submodule K V) (hxH : x.submodule ≤ H)
    (E : Finset (Submodule K V)) (hE : E ⊆ F) (M : ℕ)
    (hdom : ∀ A ∈ E, ∃ l : RadialLine x, l.val ≤ H ⊓ A ∧
      M ≤ (RadialLine.trainingOnLine X l).card) :
    E.card*M ≤ (onPlane x X H).card * (∑ i ∈ Finset.range (d-1), Nat.card K^i) := by
  let R := richRadials x X H M
  let L := R.image Subtype.val
  have hcR : R.card*M ≤ (onPlane x X H).card :=
    rich_radial_count X H hxH R (Finset.filter_subset _ _) M (by
      intro l hl
      exact (Finset.mem_filter.mp hl).2)
  have hcL : L.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hL (W : Submodule K V) (hW : W ∈ L) : finrank K W = 2 := by
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hW
    exact l.property.1
  have hN := neighbor_count_by_contained_witness hdim F hF L 2 hL E hE (by
    intro A hA
    obtain ⟨l,hl,hM⟩ := hdom A hA
    refine ⟨l.val,Finset.mem_image.mpr ⟨l,?_,rfl⟩,hl.trans inf_le_right⟩
    refine Finset.mem_filter.mpr ⟨?_,hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := RadialLine x) l, hl.trans inf_le_left⟩)
  rw [hcL] at hN
  have he : d+1-2 = d-1 := by omega
  rw [he] at hN
  calc
    E.card*M ≤ (R.card*(∑ i ∈ Finset.range (d-1), Nat.card K^i))*M := Nat.mul_le_mul_right _ hN
    _ = (R.card*M)*(∑ i ∈ Finset.range (d-1), Nat.card K^i) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hcR

end SharpRamseyFive.ActualOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Pairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

omit [Finite K] in
lemma dominant_witness (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) (hxA : x.submodule ≤ A) (hxB : x.submodule ≤ B)
    {δ a : ℝ} (hδ : 0 < δ) (ha : a ≤ δ*(pairPoints x X A B).card)
    (hnd : ¬∀ l : RadialLine x,
      2*((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card ≤
        (pairPoints x X A B).card) :
    ∃ l : RadialLine x, l.val ≤ A ⊓ B ∧
      ⌈a/(2*δ)⌉₊ ≤ (RadialLine.trainingOnLine X l).card := by
  classical
  push Not at hnd
  obtain ⟨l,hl⟩ := hnd
  have hp : 0 < ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val).card := by omega
  obtain ⟨y,hy⟩ := Finset.card_pos.mp hp
  obtain ⟨hyP,hyl⟩ := Finset.mem_filter.mp hy
  have hyAB : y.val.submodule ≤ A ⊓ B := (Finset.mem_filter.mp hyP).2
  have he : RadialLine.through x y.val y.property = l :=
    (RadialLine.through_eq_iff y.property l).mpr hyl
  refine ⟨l,?_,?_⟩
  · rw [←he]
    exact (RadialLine.through_le_iff _ _).mpr ⟨le_inf hxA hxB,hyAB⟩
  · have hs : ((pairPoints x X A B).filter fun y => y.val.submodule ≤ l.val) ⊆
        RadialLine.trainingOnLine X l := by
      intro z hz
      obtain ⟨hzP,hzl⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzP).1,hzl⟩
    have hc := Finset.card_le_card hs
    have hcr : (pairPoints x X A B).card < 2*((RadialLine.trainingOnLine X l).card:ℝ) := by
      exact_mod_cast (by omega : (pairPoints x X A B).card < 2*(RadialLine.trainingOnLine X l).card)
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (mul_pos (by norm_num) hδ)).mpr
    nlinarith

end SharpRamseyFive.WeightedOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DegreeCountFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry HyperplaneOverlap NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

theorem degree_count_four [Fintype (RadialLine x)] (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    ((neighbors x X F H δ a).card:ℝ)*a^2 ≤
      2*δ*(onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1)*a +
      2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
  classical
  let E := neighbors x X F H δ a
  let nd (A : Submodule K V) := ∀ l : RadialLine x,
    2*((pairPoints x X H A).filter fun y => y.val.submodule ≤ l.val).card ≤
      (pairPoints x X H A).card
  let N := E.filter nd
  let D := E.filter (fun A => ¬nd A)
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hne (A) (hA : A ∈ E) : H ≠ A := (Finset.mem_filter.mp hA).2.1
  have hM (A) (hA : A ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X H A).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hA).2.2))
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH N
    ((Finset.filter_subset _ _).trans hE) (fun A hA => hne A (Finset.mem_filter.mp hA).1)
    ⌈a/δ⌉₊ (fun A hA => hM A (Finset.mem_filter.mp hA).1)
    (fun A hA => (Finset.mem_filter.mp hA).2)
  have hD := dominant_degree_count x (d := 4) hdim X F hF H hxH D
    ((Finset.filter_subset _ _).trans hE) ⌈a/(2*δ)⌉₊ (by
      intro A hA
      obtain ⟨hA,hn⟩ := Finset.mem_filter.mp hA
      exact dominant_witness x X H A hxH (hxF A (hE hA)) hδ
        (Finset.mem_filter.mp hA).2.2 hn)
  have hQ : (∑ i ∈ Finset.range (4-1), Nat.card K^i) = Nat.card K^2+Nat.card K+1 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ] at hD
  have hcD : (D.card:ℝ)*⌈a/(2*δ)⌉₊ ≤ (onPlane x X H).card *
      ((Nat.card K:ℝ)^2+Nat.card K+1) := by exact_mod_cast hD
  have hcN : (N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤
      2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1) := by exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  have hceil₂ : a ≤ 2*δ*(⌈a/(2*δ)⌉₊:ℝ) :=
    ((div_le_iff₀ (mul_pos (by norm_num) hδ)).mp (Nat.le_ceil (a/(2*δ)))).trans_eq (mul_comm _ _)
  have hD' : (D.card:ℝ)*a ≤
      2*δ*(onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1) := by
    calc
      _ ≤ (D.card:ℝ)*(2*δ*⌈a/(2*δ)⌉₊) := mul_le_mul_of_nonneg_left hceil₂ (by positivity)
      _ = 2*δ*((D.card:ℝ)*⌈a/(2*δ)⌉₊) := by ring
      _ ≤ 2*δ*((onPlane x X H).card*((Nat.card K:ℝ)^2+Nat.card K+1)) :=
        mul_le_mul_of_nonneg_left hcD (by positivity)
      _ = _ := by ring
  have hN' : (N.card:ℝ)*a^2 ≤ 2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
    calc
      _ ≤ (N.card:ℝ)*(δ*⌈a/δ⌉₊)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hceil 2) (by positivity)
      _ = δ^2*((N.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
      _ ≤ δ^2*(2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
      _ = _ := by ring
  have he : N.card+D.card=E.card := Finset.card_filter_add_card_filter_not nd
  have her : (N.card:ℝ)+(D.card:ℝ)=E.card := by exact_mod_cast he
  change (E.card:ℝ)*a^2 ≤ _
  rw [←her,add_mul]
  have hDa := mul_le_mul_of_nonneg_right hD' ha
  nlinarith

theorem nondominant_weighted_degree (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 4)
    (hxF : ∀ A ∈ F, x.submodule ≤ A)
    (H : Submodule K V) (hH : finrank K H = 4) (hxH : x.submodule ≤ H)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a)
    (hline : ∀ l : RadialLine x, δ*(RadialLine.trainingOnLine X l).card < a/2) :
    ((neighbors x X F H δ a).card:ℝ)*a^2 ≤
      2*δ^2*(onPlane x X H).card^2*((Nat.card K:ℝ)+1) := by
  classical
  let E := neighbors x X F H δ a
  have hE : E ⊆ F := Finset.filter_subset _ _
  have hM (A) (hA : A ∈ E) : ⌈a/δ⌉₊ ≤ (pairPoints x X H A).card :=
    Nat.ceil_le.mpr ((div_le_iff₀ hδ).mpr (by
      simpa only [mul_comm] using (Finset.mem_filter.mp hA).2.2))
  have hN := nondominant_degree_count x hdim X F hF hxF H hH hxH E hE
    (fun A hA => (Finset.mem_filter.mp hA).2.1) ⌈a/δ⌉₊ hM (by
      intro A hA
      by_contra hn
      obtain ⟨l,_,hl⟩ := dominant_witness x X H A hxH (hxF A (hE hA)) hδ
        (Finset.mem_filter.mp hA).2.2 hn
      have hlg : a/(2*δ) ≤ ((RadialLine.trainingOnLine X l).card:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hl)
      have hh := (div_le_iff₀ (mul_pos (by norm_num) hδ)).mp hlg
      have hh' := hline l
      nlinarith)
  have hcN : (E.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2 ≤
      2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1) := by exact_mod_cast hN
  have hceil : a ≤ δ*(⌈a/δ⌉₊:ℝ) :=
    ((div_le_iff₀ hδ).mp (Nat.le_ceil (a/δ))).trans_eq (mul_comm _ _)
  calc
    _ ≤ (E.card:ℝ)*(δ*⌈a/δ⌉₊)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hceil 2) (by positivity)
    _ = δ^2*((E.card:ℝ)*(⌈a/δ⌉₊:ℝ)^2) := by ring
    _ ≤ δ^2*(2*((onPlane x X H).card:ℝ)^2*((Nat.card K:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hcN (sq_nonneg _)
    _ = _ := by ring

end SharpRamseyFive.WeightedOverlap

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

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
lemma mass_nonneg (rate : ι → ℝ≥0) (s : Finset ι) : 0 ≤ mass rate s := by
  exact Finset.sum_nonneg (fun i _ => (rate i).coe_nonneg)

end SharpRamseyFive.PoissonScore
end

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

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators

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

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DegreeStrengthCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma degree_strength_count_le (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) :
    (Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card ≤
    (WeightedOverlap.neighbors x X (F.image fun b => LinearMap.ker b.rep)
      (LinearMap.ker H.val.rep) δ a).card := by
  let E := Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))
  let G := WeightedOverlap.neighbors x X (F.image fun b => LinearMap.ker b.rep)
      (LinearMap.ker H.val.rep) δ a
  let f (p : E) : G := ⟨LinearMap.ker p.val.val.rep,by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_,p.val.property,rfl⟩,?_,?_⟩
    · intro h
      exact (Finset.mem_filter.mp p.property).2.1 (Subtype.ext (kernel_injective h))
    · have hp := (Finset.mem_filter.mp p.property).2.2
      rwa [mass_pairPoints x X δ F hF] at hp⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply Subtype.ext
    exact kernel_injective (congrArg (fun z : G => z.val) he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [Finite K]

theorem score_degree_four (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a) :
    ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a^2 ≤
      2*PoissonScore.mass (radialWeight x X δ) (pencilLines x F H)*
        ((Nat.card K:ℝ)^2+Nat.card K+1)*a +
      2*(PoissonScore.mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep) = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.degree_count_four x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ) ha)
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rw [hm]
  nlinarith [hh]

theorem score_degree_truncated (hdim : finrank K V = 5)
    (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H)
    (H : F) (a : ℝ) (ha : 0≤a)
    (hline : ∀ l : RadialLine x, (radialWeight x X δ l:ℝ) < a/2) :
    ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ)*a^2 ≤
      2*(PoissonScore.mass (radialWeight x X δ) (pencilLines x F H))^2*((Nat.card K:ℝ)+1) := by
  let G := F.image fun b => LinearMap.ker b.rep
  have hdG (A) (hA : A ∈ G) : finrank K A = 4 := by
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hA
    have := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
    omega
  have hxG (A) (hA : A ∈ G) : x.submodule ≤ A := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    exact hF b hb
  have hdH : finrank K (LinearMap.ker H.val.rep) = 4 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero H.val.rep_nonzero
    omega
  have hc : ((Finset.univ.filter (fun H' : F => H ≠ H' ∧ a ≤
      PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))).card:ℝ) ≤
      (WeightedOverlap.neighbors x X G (LinearMap.ker H.val.rep) δ a).card := by
    exact_mod_cast degree_strength_count_le x X δ F hF H a
  have hh := (mul_le_mul_of_nonneg_right hc (sq_nonneg a)).trans
    (WeightedOverlap.nondominant_weighted_degree x hdim X G hdG hxG _ hdH
      (hF H.val H.property) (by exact_mod_cast hδ) ha (by
        intro l
        simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using hline l))
  have hm : PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ)*(NondominantOverlap.onPlane x X (LinearMap.ker H.val.rep)).card := by
    rw [mass_pencil x X δ F hF]
    rfl
  rw [hm]
  nlinarith [hh]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PencilFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

theorem degree_power_two_hundred {q m a D : ℝ} (hq : 1 ≤ q)
    (hm : 0 ≤ m) (hm2 : m ≤ 2) (ha : 0 ≤ a)
    (hgeom : D*a^2 ≤ 2*m*(q^2+q+1)*a+2*m^2*(q+1)) :
    D*a^200  ≤  12*q^2*a^199+16*q*a^198 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hq2 : q ≤ q^2 := by nlinarith
  have hpoly : q^2+q+1 ≤ 3*q^2 := by nlinarith
  have hm4 : m^2 ≤ 4 := by nlinarith
  have hfirst : 2*m*(q^2+q+1)*a ≤ 12*q^2*a := by
    apply mul_le_mul_of_nonneg_right _ ha
    calc
      _  ≤  4*(3*q^2) := mul_le_mul (by linarith) hpoly (by positivity) (by norm_num)
      _ = _ := by ring
  have hsecond : 2*m^2*(q+1) ≤ 16*q := by
    calc
      _  ≤  8*(2*q) := mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right (hgeom.trans (add_le_add hfirst hsecond)) (pow_nonneg ha 198)
  have heL : D*a^2*a^198=D*a^200 := by ring
  have heR : (12*q^2*a+16*q)*a^198=12*q^2*a^199+16*q*a^198 := by ring
  rwa [heL,heR] at hh

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_QB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma q_le_B {q n : ℝ} (hq : 0<q) (hn : 0<n) (hcap : n≤q^3) :
    q ≤ q^4/n := by
  apply (le_div_iff₀ hn).mpr
  calc q*n ≤ q*q^3 := mul_le_mul_of_nonneg_left hcap hq.le
       _ = q^4 := by ring

lemma qsq_le_Bexp {q n χ : ℝ} (hn : 0<n)
    (hlow : n ≤ q^2*Real.exp χ) : q^2 ≤ q^4/n*Real.exp χ := by
  apply (mul_le_mul_iff_left₀ hn).mp
  calc
    _ ≤ q^2*(q^2*Real.exp χ) := mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
    _ = _ := by field_simp

theorem normalized_degree_low {q n a χ D : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0≤a) (ha2 : a≤2) (hcap : n≤q^3) (hlow : n≤q^2*Real.exp χ)
    (hexp : (10*2^200:ℝ)≤Real.exp χ)
    (hpower : D*a^200 ≤ 12*q^2*a^199+16*q*a^198) :
    D*a^200 ≤ (q^4/n)*Real.exp (2*χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hB : 0≤q^4/n := by positivity
  have h1 : 1≤Real.exp χ := by linarith
  have hbexp := le_mul_of_one_le_right hB h1
  have hqexp := (q_le_B hq0 hn hcap).trans hbexp
  have hi := mul_le_mul (qsq_le_Bexp hn hlow) (pow_le_pow_left₀ ha ha2 199)
    (pow_nonneg ha 199) (by positivity : 0≤q^4/n*Real.exp χ)
  have hj := mul_le_mul hqexp (pow_le_pow_left₀ ha ha2 198)
    (pow_nonneg ha 198) (by positivity : 0≤q^4/n*Real.exp χ)
  apply hpower.trans
  calc
    _ = 12*(q^2*a^199)+16*(q*a^198) := by ring
    _ ≤ 12*(q^4/n*Real.exp χ*2^199)+16*(q^4/n*Real.exp χ*2^198) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num))
        (mul_le_mul_of_nonneg_left hj (by norm_num))
    _ = 10*2^200*(q^4/n)*Real.exp χ := by ring
    _ ≤ Real.exp χ*(q^4/n)*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hB) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add]; ring

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoreDegreeLowNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

theorem score_degree_low_normalized (hdim : finrank K V=5)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F)
    (n a χ : ℝ) (hn : 0<n) (ha : 0≤a) (ha2 : a≤2)
    (hm : mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (hcap : n≤(Nat.card K:ℝ)^3) (hlow : n≤(Nat.card K:ℝ)^2*Real.exp χ)
    (hchi : (10*2^200:ℝ)≤Real.exp χ) :
    ((Finset.univ.filter fun H' : F => H≠H' ∧ a≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)*Real.exp (2*χ) := by
  have hq : (1:ℝ)≤Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0<Nat.card K)
  apply ScoreScalars.normalized_degree_low hq hn ha ha2 hcap hlow hchi
  exact ScoreScalars.degree_power_two_hundred hq (mass_nonneg _ _) hm ha
    (score_degree_four x hdim X δ hδ F hF H a ha)

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

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

end SharpRamseyFive.ScoreGeometry

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
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialOffException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in

lemma radial_lt_off_exception (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (L : Finset (Submodule K V))
    (hL : ∀ l : RadialLine x,l.val∈L) (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ a L Q 1) (l : RadialLine x) :
    (radialWeight x (outsideAt x S (O x)) δ l:ℝ)< a := by
  by_contra hn
  have hw : a≤(δ:ℝ)*((RadialLine.trainingOnLine (outsideAt x S (O x)) l).card:ℝ) := by
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast] using le_of_not_gt hn
  have hl : l.val∈localLines S O δ a L x := by
    refine Finset.mem_filter.mpr ⟨hL l,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.property.2
    · change a≤(δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule≤ l.val).card:ℝ) at hw
      rwa [outsideAt_filter_card] at hw
  have hc : (1:ℝ)≤(localLines S O δ a L x).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨l.val,hl⟩
  exact hgood (Finset.mem_filter.mpr ⟨hx,hc⟩)

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
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

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptionScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_plane_ambient_margins {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
      let Q := P η σ D R
      let a := 1/(100*(momentOrder σ Q:ℝ))
      100000000≤Q/10000 ∧ Q/10000<σ/2-4*Q ∧
      20*Q≤σ/2-4*Q ∧ Real.exp (-Q)≤a ∧ a≤2 ∧ (1332096:ℝ)≤Real.exp Q := by
  have hh := eventually_hierarchy hη hη' 0 (1/100) 1000000000000 (by norm_num) (by norm_num)
  have ha := eventually_power_absorption hη hη' 1000200 1 1 (by norm_num) (by norm_num) (by norm_num)
  have hc := eventually_power_absorption hη hη' 1332096 0 1 (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hh,ha,hc] with σ hσ hh ha hc
  intro D R hr
  have hh := hh D R 0 0 hr (by simp) (by positivity)
  have ha := ha D R hr
  have hc := hc D R hr
  dsimp only
  have hL : 0≤L η σ D := by linarith only [hh.1]
  have hLP : L η σ D≤P η σ D R := by linarith only [hh.2.2.2.2.2,hL]
  have hP : 1≤P η σ D R := by linarith only [hh.1,hLP]
  have hp := momentOrder_bounds hσ hP
  have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
  have hp1 : (1:ℝ)≤ momentOrder σ (P η σ D R) := by exact_mod_cast hp.2.1
  refine ⟨by linarith only [hh.1,hLP],by linarith only [hh.2.1,hP],by linarith only [hh.2.1,hP],?_,?_,?_⟩
  · rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))
    calc
      _≤100*(10002*σ) := mul_le_mul_of_nonneg_left hp.2.2.2.2 (by norm_num)
      _=1000200*σ := by ring
      _≤_ := by simpa only [Real.rpow_one,one_mul] using ha
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(momentOrder σ (P η σ D R):ℝ))).mpr
    linarith only [hp1]
  · simpa only [Real.rpow_zero,mul_one,one_mul] using hc
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_DimensionFourStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma four_strong_normalize {N q n a P : ℝ} {k : ℕ} (hq : 0<q) (hn : 0<n) (ha : 0<a)
    (hN : N*a^2≤40*q^k) (hsmall : n≤q^(4-k)*Real.exp (-4*P))
    (hk : k≤4) (habs : 40/a^2≤Real.exp P) : N≤(q^4/n)*Real.exp (-3*P) := by
  have h₁ : N≤q^k*Real.exp P := by
    calc
      N≤40*q^k/a^2 := (le_div_iff₀ (sq_pos_of_pos ha)).mpr hN
      _=q^k*(40/a^2) := by ring
      _≤q^k*Real.exp P := mul_le_mul_of_nonneg_left habs (pow_nonneg hq.le k)
  apply h₁.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  calc
    _≤(q^k*Real.exp P)*(q^(4-k)*Real.exp (-4*P)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _=(q^k*q^(4-k))*(Real.exp P*Real.exp (-4*P)) := by ring
    _=q^4*Real.exp (-3*P) := by rw [←pow_add,Nat.add_sub_of_le hk,←Real.exp_add];congr 2;ring
end SharpRamseyFive.ScoreScalars
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence GlobalRadial PoissonScore WeightedPrograms
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_ambient_degree {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V)) (δ : ℝ≥0)
      (F : Finset (ℙ K (Dual K V))) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ → Range η σ D R →
      S.Nonempty → (S.card:ℝ)≤10*Real.exp (5*σ/2) → 0<δ →
      (∀H∈F,Incident x H) →
      (∀H:F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H)≤2) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      (x∉badCenters S O δ ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 ∨
        (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P η σ D R)) →
      ∀H:F,((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(momentOrder σ (P η σ D R):ℝ))≤ mass
        (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        ((Nat.card K:ℝ)^4/S.card)*Real.exp (-3*P η σ D R) := by
  have he := eventually_power_absorption hη hη' (40*1000200^2) 2 1
    (by positivity) (by norm_num) (by norm_num)
  have hm := eventually_plane_ambient_margins hη hη'
  filter_upwards [eventually_ge_atTop (100:ℝ),he,hm] with σ hσ he hm
  intro D R K V _ _ _ _ _ x _ S O δ F Lines Q hdim hq hr hS hn hδ hF hmass hLines hxQ hstrong H
  have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn0 : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hm := hm D R hr
  have hP1 : 1≤P η σ D R := by linarith only [hm.1]
  have hp := momentOrder_bounds (by linarith only [hσ]) hP1
  have hp0 : (0:ℝ)< momentOrder σ (P η σ D R) := Nat.cast_pos.mpr hp.2.1
  let a : ℝ := 1/(100*(momentOrder σ (P η σ D R):ℝ))
  have ha : 0<a := by dsimp [a];positivity
  have ha2 : a≤2 := hm.2.2.2.2.1
  have habs : 40/a^2≤Real.exp (P η σ D R) := by
    have he := he D R hr
    rw [Real.rpow_two] at he
    calc
      40/a^2=40*(100*(momentOrder σ (P η σ D R):ℝ))^2 := by dsimp [a];field_simp
      _≤40*(100*(10002*σ))^2 := by gcongr;exact hp.2.2.2.2
      _=(40*1000200^2)*σ^2 := by ring
      _≤_ := by simpa only [one_mul] using he
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3*Real.exp (-4*P η σ D R) := by
    have he10 : (10:ℝ)≤Real.exp (P η σ D R) := by linarith only [hm.2.2.2.2.2]
    calc
      _≤10*Real.exp (5*σ/2) := hn
      _≤Real.exp (P η σ D R)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he10 (Real.exp_nonneg _)
      _=Real.exp (P η σ D R+5*σ/2) := (Real.exp_add _ _).symm
      _≤Real.exp (3*σ-4*P η σ D R) := Real.exp_le_exp.mpr (by linarith only [hm.2.2.1,hP1])
      _=_ := by rw [hq,←Real.exp_nat_mul,←Real.exp_add];congr 1;norm_num;ring
  let N : ℝ := (Finset.univ.filter fun H':F => H≠H' ∧ a≤ mass
    (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H∩pencilLines x F H')).card
  change N≤_
  rcases hstrong with hstrong|hsmall
  · have hh := score_degree_truncated x hdim (outsideAt x S (O x)) δ hδ F hF H a ha.le
      (radial_lt_off_exception x S O δ (a/2) Lines hLines Q hxQ hstrong)
    have hmsq : (mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤4 := by
      calc
        _≤(2:ℝ)^2 := pow_le_pow_left₀ (mass_nonneg _ _) (hmass H) 2
        _=4 := by norm_num
    have hN : N*a^2≤40*(Nat.card K:ℝ)^1 := by
      have hh := hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hmsq] : 2*(mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤8) (by positivity))
      change N*a^2≤8*((Nat.card K:ℝ)+1) at hh
      simp only [pow_one];linarith only [hh,hq1]
    exact ScoreScalars.four_strong_normalize hq0 hn0 ha hN hcap (by norm_num) habs
  · have hh := score_degree_four x hdim (outsideAt x S (O x)) δ hδ F hF H a ha.le
    have hq2 : (Nat.card K:ℝ)≤(Nat.card K:ℝ)^2 := le_self_pow₀ hq1 (by norm_num : (2:ℕ)≠0)
    have hq3 : (Nat.card K:ℝ)^2+Nat.card K+1≤3*(Nat.card K:ℝ)^2 := by nlinarith only [hq1,hq2]
    have hmsq : (mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H))^2≤4 := by
      calc
        _≤(2:ℝ)^2 := pow_le_pow_left₀ (mass_nonneg _ _) (hmass H) 2
        _=4 := by norm_num
    have hN : N*a^2≤40*(Nat.card K:ℝ)^2 := by
      apply hh.trans
      calc
        _≤2*2*(3*(Nat.card K:ℝ)^2)*2+2*4*((Nat.card K:ℝ)+1) := by gcongr;exact hmass H
        _≤40*(Nat.card K:ℝ)^2 := by nlinarith only [hq1,hq2]
    exact ScoreScalars.four_strong_normalize hq0 hn0 ha hN hsmall (by norm_num) habs
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionFourLowAmbient
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

theorem eventually_four_low_ambient_tail_oai {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (O : ℙ K V→Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
      (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (t : ℝ),
      finrank K V=5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      O x=C a∪C b → (S.card:ℝ) ≤ 10*Real.exp (5*σ/2) →
      (S.card:ℝ) ≤ (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=4) S C ((L₀:ℝ)/100) →
      (∀l : RadialLine x,l.val∈Lines) → x∈Q →
      x∉radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) →
      (x∉badCenters S O (pointStrength S) ((1/(100*(momentOrder σ (P η σ D R):ℝ)))/2) Lines Q 1 ∨
        (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P η σ D R)) →
      scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      (scheduleMeasure (fun _ : S => L₀*pointStrength S) R).real
        {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
        (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have ht := eventually_low_original_tail hη hη' Cb hCb
  have hd := eventually_dyad_power_payment hη hη'
  have hc := eventually_power_absorption hη hη' (11*2^200) 0 (1/200)
    (by positivity) (by norm_num) (by norm_num)
  have hs := eventually_four_ambient_degree hη hη'
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,hd,hc,hs] with σ hσ ht hd hc hs
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c O F Lines Q t
    hdim hq hr hL hb₀ hbhi hτ hS ha hb hC hO hSn hLow hn hf hF hx hLines hxQ hgood hstrong ht₀
  have hS0 : (0:ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hδ : 0 < pointStrength (K:=K) S := by
    rw [←NNReal.coe_pos,coe_pointStrength]
    exact div_pos (by exact_mod_cast Nat.card_pos (α:=K)) hS0
  have hlarge : (11*2^200:ℝ) ≤ Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,div_eq_mul_inv,one_mul,mul_comm (200⁻¹:ℝ)] using hc D R hr
  have hcard : ((outsideAt x S (O x)).card:ℝ) ≤ Real.exp (3*σ) := by
    have he : (10:ℝ) ≤ Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
    calc
      _ ≤ (S.card:ℝ) := Nat.cast_le.mpr (outsideAt_card_le x S (O x))
      _ ≤ 10*Real.exp (5*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm (H:F) : mass (radialWeight x (outsideAt x S (O x)) (pointStrength S)) (pencilLines x F H) ≤ 2 := by
    rw [hO]
    exact (actual_radial_mass_bounds x S C hS a b c ha hb hC F hF hf hn H).2.2.trans (by norm_num)
  have hP0 : 0≤P η σ D R := by unfold P;rw [←hL];positivity
  have hmass : (pointStrength (K:=K) S:ℝ)*S.card≤Nat.card K := by
    rw [coe_pointStrength,div_mul_cancel₀ _ hS0.ne']
  have hlow : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp ((P η σ D R/200)/2) :=
    hLow.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hP0])) (sq_nonneg _))
  have hh := score_pair_low_moment x hdim S O (pointStrength S) hδ F
    (fun H hH => (hF H hH).1) S.card (P η σ D R/200) hS0 hmass hlow hlarge Lines hLines Q hxQ hm
    (off_radialExceptions S O (pointStrength S) Lines Q (Nat.card K) S.card (P η σ D R/200) x hgood) 200 (le_refl _)
  have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
  have hmoment : (∑z : DistinctPairs F,strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200) ≤
        (scale (K:=K) 4 S.card)^2*Real.exp (P η σ D R/50) := by
    apply hh.trans
    change 2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
      (((Nat.card K:ℝ)^4/S.card)^2*Real.exp (2*(P η σ D R/200))) ≤ _
    calc
      _ = ((Nat.card K:ℝ)^4/S.card)^2*(2^200*((Nat.clog 2 (outsideAt x S (O x)).card:ℝ)+1)*
          Real.exp (2*(P η σ D R/200))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay (sq_nonneg _)
  have hcap : (S.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2), hσ]
    calc
      _≤10*Real.exp (5*σ/2) := hSn
      _≤Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _=_ := by rw [←Real.exp_add,hq,←Real.exp_nat_mul];congr 1;norm_num;ring
  have hchi : (10*2^200:ℝ)≤Real.exp (P η σ D R/100) := by
    have hh : Real.exp (P η σ D R/200)≤Real.exp (P η σ D R/100) := Real.exp_le_exp.mpr (by linarith only [hP0])
    linarith only [hlarge,hh]
  have hlow' : (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (P η σ D R/100) :=
    hLow.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hP0])) (sq_nonneg _))
  apply ht 4 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
    ha hb hC (by convert hSn using 1; norm_num) hLow hn hf hF hx _ _ _ ht₀
  · intro u hu hu2
    have hh := power_tail_mul (fun z : DistinctPairs F => strength (pencilLines x F)
      (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z) (strength_nonneg _ _) 200 u _ hu hmoment
    simp only [hO,strength] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
  · intro H u hu hu2
    have hh := score_degree_low_normalized x hdim (outsideAt x S (O x)) (pointStrength S) hδ F
      (fun H hH => (hF H hH).1) H S.card u (P η σ D R/100) hS0 hu.le hu2 (hm H) hcap hlow' hchi
    simpa only [hO,show 2*(P η σ D R/100)=P η σ D R/50 by ring,scale] using hh
  · intro H
    have hh := hs D R K V x S O (pointStrength S) F Lines Q hdim hq hr hS hSn hδ
      (fun H hH => (hF H hH).1) hm hLines hxQ hstrong H
    simpa only [hO,scale] using hh

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_ambient_tail_oai
