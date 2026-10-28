-- Prove2me | solution 1 for OAI.TranslativeCovering.periodization_exact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:04:24.595749+00:00
-- url     : https://prove2.me/submissions/e790d649-e001-4a63-bb47-fecb3e92967b

import Mathlib
import Definitions.Def_CoveringDensity
import Definitions.Def_OAIQ16Cd002

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LatticeAveraging
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace LatticeAveraging
open Set MeasureTheory
open scoped ENNReal BigOperators Pointwise

lemma one_coset {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in F,∑' l : Λ,f (y-p-l.val) = ∫⁻ x,f x := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  rw [lintegral_tsum (f := fun l : Λ => fun y => f (y-p-l.val))
    (fun l => (hf.comp ((measurable_id.sub_const p).sub_const l.val)).aemeasurable)]
  let : VAddInvariantMeasure Λ (Space n) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Space n) volume)
  have heq := hF.lintegral_eq_tsum' (fun x => f (x-p))
  rw [lintegral_sub_right_eq_self] at heq
  apply Eq.trans _ heq.symm
  apply tsum_congr
  intro l
  congr 1
  funext y
  congr 1
  change y-p-l.val = -l.val+y-p
  abel

lemma averaging {n : ℕ} {I : Type u_3} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in F,field Λ p f y = (Fintype.card I:ℝ≥0∞)*∫⁻ x,f x := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  unfold field
  rw [lintegral_finsetSum (f := fun i : I => fun y => ∑' l : Λ, f (y-p i-l.val))
    Finset.univ (fun i _ => Measurable.tsum
    fun l => hf.comp ((measurable_id.sub_const (p i)).sub_const l.val))]
  simp_rw [one_coset Λ hF _ hf]
  simp

lemma normalized_averaging {n : ℕ} {I : Type u_5} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y,field Λ p f y ∂uniformWindow F =
      ((Fintype.card I:ℝ≥0∞)/volume F)*∫⁻ x,f x := by
  rw [uniformWindow,lintegral_smul_measure,averaging Λ hF p hf]
  simp only [div_eq_mul_inv]
  ac_rfl

lemma probability_window {n : ℕ} {F : Set (Space n)}
    (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞) :
    IsProbabilityMeasure (uniformWindow F) := by
  constructor
  rw [uniformWindow,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hF0 hFtop

end LatticeAveraging

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationWindow
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2

namespace LocalizationWindow
open Set MeasureTheory LatticeAveraging
open scoped ENNReal Pointwise BigOperators

lemma finite_occurrences {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n)
    {B : Set (Space n)} (hB : Bornology.IsBounded B) :
    {q : I×Λ | p q.1+q.2.val ∈ B}.Finite := by
  have each (i : I) : {l : Λ | p i+l.val ∈ B}.Finite := by
    have hb : Bornology.IsBounded ((fun x : Space n => -p i+x) '' B) :=
      (isometry_add_left (-p i)).lipschitz.isBounded_image hB
    have hc : IsClosed (Λ : Set (Space n)) := AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
    have hf := Metric.finite_isBounded_inter_isClosed
      (s := (Λ : Set (Space n))) DiscreteTopology.isDiscrete hb hc
    apply Set.Finite.of_injOn (f := fun l : Λ => l.val) (t := _ ∩ (Λ : Set (Space n)))
      ?_ (Subtype.val_injective.injOn) hf
    intro l hl
    refine ⟨⟨p i+l.val,hl,by simp⟩,l.property⟩
  apply (Set.finite_iUnion (fun i => (each i).image (fun l => (i,l)))).subset
  intro q hq
  exact Set.mem_iUnion.mpr ⟨q.1,⟨q.2,hq,rfl⟩⟩

end LocalizationWindow

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Periodization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering

open scoped Classical Topology

lemma isCompact_cube (n : ℕ) (R : ℝ) : IsCompact (cube n R) := by
  have h := (isCompact_pi_infinite (fun _ : Fin n => isCompact_Icc (a := -R) (b := R))).image
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, hx, WithLp.toLp_ofLp 2 x⟩
  · rintro ⟨f, hf, rfl⟩
    exact hf

lemma exists_cube_superset {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ K ⊆ cube n r := by
  obtain ⟨r, hr, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨r, hr, ?_⟩
  intro x hx i
  exact abs_le.mp ((PiLp.norm_apply_le x i).trans (hbound x hx))

lemma cube_cover_mod_period {n : ℕ} {L : ℝ} (hL : 0 < L) (a y : Space n) :
    ∃ z : Fin n → ℤ, y - cubePeriod L z - a ∈ cube n L := by
  let z : Fin n → ℤ := fun i => ⌊(y i - a i + L) / (2 * L)⌋
  refine ⟨z, ?_⟩
  intro i
  have hlo := Int.floor_le ((y i - a i + L) / (2 * L))
  have hhi := Int.lt_floor_add_one ((y i - a i + L) / (2 * L))
  have h2L : 0 < 2 * L := by positivity
  have hlo' := (le_div_iff₀ h2L).mp hlo
  have hhi' := (div_lt_iff₀ h2L).mp hhi
  change -L ≤ y i - 2 * L * (z i : ℝ) - a i ∧
    y i - 2 * L * (z i : ℝ) - a i ≤ L
  change (z i : ℝ) * (2 * L) ≤ y i - a i + L at hlo'
  change y i - a i + L < ((z i : ℝ) + 1) * (2 * L) at hhi'
  constructor <;> linarith

lemma restrict_cover_window {n : ℕ} {K X : Set (Space n)} {r L : ℝ}
    (hKr : K ⊆ cube n r) (hcover : Covers K X) (a : Space n) :
    ∀ y : Space n, y - a ∈ cube n L →
      ∃ x ∈ X ∩ {x | x - a ∈ cube n (L + r)}, y - x ∈ K := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := hcover y
  refine ⟨x, ⟨hx, ?_⟩, hyx⟩
  intro i
  have h1 := hy i
  have h2 := hKr hyx i
  simp only [PiLp.sub_apply] at h1 h2 ⊢
  constructor <;> linarith

lemma periodize_cover {n : ℕ} {K X : Set (Space n)} {r L : ℝ}
    (hL : 0 < L) (hKr : K ⊆ cube n r) (hcover : Covers K X) (a : Space n) :
    Covers K (repeatCube L (X ∩ {x | x - a ∈ cube n (L + r)})) := by
  intro y
  obtain ⟨z, hz⟩ := cube_cover_mod_period hL a y
  obtain ⟨x, hx, hyx⟩ := restrict_cover_window hKr hcover a (y - cubePeriod L z) hz
  refine ⟨x + cubePeriod L z, ⟨x, hx, z, rfl⟩, ?_⟩
  convert hyx using 1; abel

lemma finite_cover_window {n : ℕ} {X : Set (Space n)} (hX : LocallyFiniteCenters X)
    (a : Space n) (R : ℝ) : (X ∩ {x | x - a ∈ cube n R}).Finite := by
  apply hX
  have h := (isCompact_cube n R).image (continuous_id.add (continuous_const (y := a)))
  have heq : (fun y : Space n => y + a) '' cube n R = {x | x - a ∈ cube n R} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_ofPred_eq, add_sub_cancel_right] using hy
    · intro hx
      exact ⟨x - a, hx, sub_add_cancel x a⟩
  change IsCompact ((fun y : Space n => y + a) '' cube n R) at h
  rw [heq] at h
  exact h.isBounded

lemma cubicCenterInfimum_le_window {n : ℕ} {K X : Set (Space n)} {r L : ℝ}
    (hL : 0 < L) (hKr : K ⊆ cube n r) (hX : LocallyFiniteCenters X)
    (hcover : Covers K X) (a : Space n) :
    cubicCenterInfimum K ≤
      ((X ∩ {x | x - a ∈ cube n (L + r)}).ncard : ℝ≥0∞) /
        ENNReal.ofReal ((2 * L) ^ n) := by
  let hS := finite_cover_window hX a (L + r)
  let P : CubicCover K :=
    ⟨L, hL, hS.toFinset, by
      simpa only [hS.coe_toFinset] using periodize_cover hL hKr hcover a⟩
  have h := iInf_le (fun P : CubicCover K =>
    (P.centers.card : ℝ≥0∞) / ENNReal.ofReal ((2 * P.L) ^ n)) P
  simpa only [cubicCenterInfimum, P, Set.ncard_eq_toFinset_card _ hS] using h

lemma cubicCenterInfimum_le_upperIntensity {n : ℕ} {K X : Set (Space n)}
    (hK : IsCompact K) (hX : LocallyFiniteCenters X) (hcover : Covers K X) :
    cubicCenterInfimum K ≤ upperCenterIntensity X := by
  obtain ⟨r, hr, hKr⟩ := exists_cube_superset hK
  have hwindow (L : ℝ) (hL : 0 < L) :
      cubicCenterInfimum K ≤ ((X ∩ cube n (L+r)).ncard : ℝ≥0∞) /
        ENNReal.ofReal ((2*L)^n) := by
    simpa only [sub_zero, Set.ofPred_mem_eq] using cubicCenterInfimum_le_window hL hKr hX hcover 0
  have hfinite : cubicCenterInfimum K ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (hwindow 1 zero_lt_one)
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  let k := (cubicCenterInfimum K).toReal
  have hsmall (R : ℝ) (hR : r < R) :
      k ≤ ((X ∩ cube n R).ncard : ℝ) / ((2*(R-r))^n) := by
    have h := hwindow (R-r) (sub_pos.mpr hR)
    rw [sub_add_cancel, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_div_of_pos (show 0 < (2*(R-r))^n by positivity)] at h
    have ht := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr h
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ ((X ∩ cube n R).ncard : ℝ) / ((2*(R-r))^n))] using ht
  have hbound : (fun R : ℝ => ENNReal.ofReal (k * (1-r/R)^n)) ≤ᶠ[atTop]
      (fun R : ℝ => ((X ∩ cube n R).ncard : ℝ≥0∞) / ENNReal.ofReal ((2*R)^n)) := by
    filter_upwards [eventually_gt_atTop r] with R hR
    have hR0 : 0 < R := hr.trans hR
    have heq : (1-r/R)*(2*R) = 2*(R-r) := by field_simp
    have hl : k * (1-r/R)^n ≤ ((X ∩ cube n R).ncard : ℝ) / ((2*R)^n) := by
      apply (le_div_iff₀ (show 0 < (2*R)^n by positivity)).mpr
      rw [mul_assoc, ← mul_pow, heq]
      exact (le_div_iff₀ (show 0 < (2*(R-r))^n by positivity)).mp (hsmall R hR)
    have ht := ENNReal.ofReal_le_ofReal hl
    rwa [ENNReal.ofReal_div_of_pos (show 0 < (2*R)^n by positivity),
      ENNReal.ofReal_natCast] at ht
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal (k * (1-r/R)^n)) atTop
      (𝓝 (cubicCenterInfimum K)) := by
    have hratio : Tendsto (fun R : ℝ => 1-r/R) atTop (𝓝 1) := by
      simpa only [sub_zero, id_eq] using tendsto_const_nhds.sub (tendsto_id.const_div_atTop r)
    have ht := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := k)).mul (hratio.pow n))
    simpa only [one_pow, mul_one, k, ENNReal.ofReal_toReal hfinite] using ht
  calc
    cubicCenterInfimum K = limsup (fun R : ℝ => ENNReal.ofReal (k * (1-r/R)^n)) atTop :=
      hlim.limsup_eq.symm
    _ ≤ upperCenterIntensity X := limsup_le_limsup hbound

lemma cubic_density_le_thetaT {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    volume K * cubicCenterInfimum K ≤ thetaT K := by
  apply le_iInf
  intro X
  exact mul_le_mul le_rfl (cubicCenterInfimum_le_upperIntensity hK X.property.1
    X.property.2) bot_le bot_le

lemma card_integerGrid (n N : ℕ) : (integerGrid n N).card = (2*N+1)^n := by
  simp only [integerGrid, Fintype.card_piFinset, Int.card_Icc]
  have h : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2*N+1 := by omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma repeatCube_window_subset {n : ℕ} {L r R : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) (hS : (S : Set (Space n)) ⊆ cube n r) :
    repeatCube L (S : Set (Space n)) ∩ cube n R ⊆
      ((S ×ˢ integerGrid n ⌈(R+r)/(2*L)⌉₊).image
        (fun sz => sz.1 + cubePeriod L sz.2) : Set (Space n)) := by
  intro x hx
  obtain ⟨s, hs, z, rfl⟩ := hx.1
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨(s,z), Finset.mem_product.mpr ⟨hs, ?_⟩, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have h1 := hx.2 i
  have h2 := hS hs i
  change -R ≤ s i + 2*L*(z i : ℝ) ∧ s i + 2*L*(z i : ℝ) ≤ R at h1
  have hceil := Nat.le_ceil ((R+r)/(2*L))
  have hc := (div_le_iff₀ (show 0 < 2*L by positivity)).mp hceil
  have hz : -(⌈(R+r)/(2*L)⌉₊ : ℝ) ≤ (z i : ℝ) ∧
      (z i : ℝ) ≤ (⌈(R+r)/(2*L)⌉₊ : ℝ) := by
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  exact_mod_cast hz

lemma repeatCube_window_finite {n : ℕ} {L : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) (R : ℝ) : (repeatCube L (S : Set (Space n)) ∩ cube n R).Finite := by
  obtain ⟨r, -, hr⟩ := exists_cube_superset S.finite_toSet.isCompact
  exact (Finset.finite_toSet _).subset (repeatCube_window_subset (R := R) hL S hr)

lemma repeatCube_locallyFinite {n : ℕ} {L : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) : LocallyFiniteCenters (repeatCube L (S : Set (Space n))) := by
  intro B hB
  obtain ⟨R, -, hR⟩ := hB.exists_pos_norm_le
  apply (repeatCube_window_finite hL S R).subset
  intro x hx
  exact ⟨hx.1, fun i => abs_le.mp ((PiLp.norm_apply_le x i).trans (hR x hx.2))⟩

lemma repeatCube_count_le {n : ℕ} {L r R : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) (hS : (S : Set (Space n)) ⊆ cube n r) :
    (repeatCube L (S : Set (Space n)) ∩ cube n R).ncard ≤ S.card * (2*⌈(R+r)/(2*L)⌉₊+1)^n := by
  have h := Set.ncard_le_ncard (repeatCube_window_subset (R := R) hL S hS)
  rw [Set.ncard_coe_finset] at h
  exact h.trans (Finset.card_image_le.trans_eq (by
    rw [Finset.card_product, card_integerGrid]))

lemma repeatCube_count_le_real {n : ℕ} {L r R : ℝ} (hL : 0 < L)
    (hrR : 0 ≤ R+r) (S : Finset (Space n)) (hS : (S : Set (Space n)) ⊆ cube n r) :
    ((repeatCube L (S : Set (Space n)) ∩ cube n R).ncard : ℝ) ≤
      (S.card : ℝ) * ((R+r)/L+3)^n := by
  have h := (Nat.cast_le (α := ℝ)).mpr (repeatCube_count_le (R := R) hL S hS)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  have hc := Nat.ceil_lt_add_one (div_nonneg hrR (by positivity : 0 ≤ 2*L))
  have he : 2*((R+r)/(2*L)) = (R+r)/L := by field_simp
  linarith

lemma upperIntensity_repeatCube_le {n : ℕ} {L : ℝ} (hL : 0 < L)
    (S : Finset (Space n)) :
    upperCenterIntensity (repeatCube L (S : Set (Space n))) ≤
      (S.card : ℝ≥0∞) / ENNReal.ofReal ((2*L)^n) := by
  obtain ⟨r, hr, hS⟩ := exists_cube_superset S.finite_toSet.isCompact
  let b : ℝ → ℝ := fun R => (S.card : ℝ) * (((R+r)/L+3)/(2*R))^n
  have hb : ∀ᶠ R : ℝ in atTop,
      ((repeatCube L (S : Set (Space n)) ∩ cube n R).ncard : ℝ≥0∞) /
        ENNReal.ofReal ((2*R)^n) ≤ ENNReal.ofReal (b R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hcnt := repeatCube_count_le_real hL (by linarith : 0 ≤ R+r) S hS
    have hp : 0 < (2*R)^n := pow_pos (by linarith) _
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hp]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((S.card : ℝ)*((R+r)/L+3)^n)/(2*R)^n :=
        div_le_div_of_nonneg_right hcnt hp.le
      _ = b R := by dsimp [b]; rw [div_pow]; ring
  have hratio : Tendsto (fun R : ℝ => ((R+r)/L+3)/(2*R)) atTop
      (𝓝 (1/(2*L))) := by
    have ht : Tendsto (fun R : ℝ => (1+(r+3*L)/R)/(2*L)) atTop
        (𝓝 (1/(2*L))) := by
      simpa only [add_zero, id_eq] using
        (tendsto_const_nhds.add (tendsto_id.const_div_atTop (r+3*L))).div_const (2*L)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp
    ring
  have ht : Tendsto (fun R => ENNReal.ofReal (b R)) atTop
      (𝓝 ((S.card : ℝ≥0∞)/ENNReal.ofReal ((2*L)^n))) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (S.card : ℝ))).mul (hratio.pow n))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [one_div_pow, mul_one_div, ENNReal.ofReal_div_of_pos (pow_pos (by positivity) n)]
    simp only [ENNReal.ofReal_natCast]
  exact (limsup_le_limsup hb).trans_eq ht.limsup_eq

theorem thetaT_eq_cubic {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hvol : volume K ≠ ∞) (hvol0 : volume K ≠ 0) :
    thetaT K = volume K * cubicCenterInfimum K := by
  apply le_antisymm _ (cubic_density_le_thetaT hK)
  rw [cubicCenterInfimum, ENNReal.mul_iInf_of_ne hvol0 hvol]
  apply le_iInf
  intro P
  let X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X} :=
    ⟨repeatCube P.L (P.centers : Set (Space n)),
      repeatCube_locallyFinite P.positive P.centers, P.covers⟩
  exact (iInf_le (fun X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X} =>
    volume K * upperCenterIntensity X.val) X).trans
      (mul_le_mul le_rfl (upperIntensity_repeatCube_le P.positive P.centers) bot_le bot_le)

theorem periodization {n : ℕ} {K : Set (Space n)} (hK : ConvexBody K) :
    thetaT K = volume K * cubicCenterInfimum K := by
  apply thetaT_eq_cubic hK.1 hK.1.measure_lt_top.ne
  exact ne_of_gt ((isOpen_interior.measure_pos volume hK.2.2).trans_le
    (measure_mono interior_subset))

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CubicLattice
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace CubicLattice
open Module Set MeasureTheory TranslativeCovering
open scoped ENNReal BigOperators Classical
lemma volume_domain {n : ℕ} {L : ℝ} (hL : 0<L) :
    volume (ZSpan.fundamentalDomain (basis n L hL)) = ENNReal.ofReal ((2*L)^n) := by
  let b₀ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hv : volume (ZSpan.fundamentalDomain b₀)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ volume)]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).volume_parallelepiped
  rw [ZSpan.measure_fundamentalDomain (basis n L hL) volume b₀,hv,mul_one]
  congr 1
  have he : (basis n L hL : Fin n → Space n) = fun i => (2*L) • b₀ i := funext (basis_apply hL)
  rw [he,AlternatingMap.map_smul_univ,Basis.det_self]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  exact abs_of_nonneg (pow_nonneg (by positivity) _)

end CubicLattice

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PeriodicEquality
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5

namespace PeriodicEquality
open Set Filter MeasureTheory TranslativeCovering LatticeAveraging LocalizationWindow
open scoped ENNReal Topology BigOperators Classical

lemma volume_cube (n : ℕ) {R : ℝ} (hR : 0≤R) :
    volume (cube n R) = ENNReal.ofReal ((2*R)^n) := by
  have he : cube n R = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)) := by
    ext x
    simp only [cube,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_true_left,Set.mem_Icc]
  rw [he,(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet),volume_pi,Measure.pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

lemma locallyFinite {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n) :
    LocallyFiniteCenters (centers Λ p) := by
  intro B hB
  apply ((finite_occurrences Λ p hB).image (fun q : I×Λ => p q.1+q.2.val)).subset
  rintro x ⟨⟨i,l,rfl⟩,hx⟩
  exact ⟨(i,l),hx,rfl⟩

lemma count_le_field {n : ℕ} {I : Type u_3} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n)
    (z : Space n) (R : ℝ) :
    ((centers Λ p ∩ {x | x-z∈cube n R}).ncard:ℝ≥0∞) ≤
      field Λ p ((cube n R).indicator (fun _ => 1)) z := by
  let B : Set (Space n) := {x | x-z ∈ cube n R}
  have hB : Bornology.IsBounded B := by
    have he : B = (fun x : Space n => x+z) '' cube n R := by
      ext x; constructor
      · intro hx; exact ⟨x-z,hx,sub_add_cancel x z⟩
      · rintro ⟨x,hx,rfl⟩; simpa only [B,mem_ofPred_eq,add_sub_cancel_right] using hx
    rw [he]
    exact ((isCompact_cube n R).image (continuous_id.add continuous_const)).isBounded
  let S : Finset (I×Λ) := (finite_occurrences Λ p hB).toFinset
  have hcard : (centers Λ p ∩ B).ncard≤S.card := by
    have hs : centers Λ p ∩ B ⊆ (S.image (fun q => p q.1+q.2.val) : Set (Space n)) := by
      rintro x ⟨⟨i,l,rfl⟩,hx⟩
      exact Finset.mem_image.mpr ⟨(i,l),by simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq] using hx,rfl⟩
    exact (Set.ncard_le_ncard hs).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=S) (f:=fun q => p q.1+q.2.val))
  have he : ∑ q ∈ S,(cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val) = (S.card:ℝ≥0∞) := by
    have hf (q : I×Λ) (hq : q∈S) : (cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val)=1 := by
      have hx : p q.1+q.2.val-z ∈ cube n R := by simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq,B] using hq
      apply Set.indicator_of_mem
      intro i
      have hh := hx i
      change -R ≤ z i-p q.1 i-q.2.val i ∧ z i-p q.1 i-q.2.val i≤R
      change -R ≤ p q.1 i+q.2.val i-z i ∧ p q.1 i+q.2.val i-z i≤R at hh
      constructor <;> linarith only [hh.1,hh.2]
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using Finset.sum_congr rfl hf
  calc
    _ ≤ (S.card:ℝ≥0∞) := by exact_mod_cast hcard
    _ = ∑ q∈S,(cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val) := he.symm
    _ ≤ ∑' q : I×Λ,(cube n R).indicator (fun _ => (1:ℝ≥0∞)) (z-p q.1-q.2.val) := ENNReal.sum_le_tsum S
    _ = _ := by rw [ENNReal.tsum_prod',tsum_fintype]; rfl

lemma cubic_le_periodic_window {n : ℕ} {I : Type u_4} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F K : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    {r L : ℝ} (hL : 0<L) (hKr : K⊆cube n r) (hLr : 0≤L+r)
    (hc : ∀ y,∃ (i:I) (l:Λ),y-p i-l.val∈K) :
    cubicCenterInfimum K ≤ ((Fintype.card I:ℝ≥0∞)/volume F)*
      ENNReal.ofReal (((L+r)/L)^n) := by
  have hcover : Covers K (centers Λ p) := by
    intro y
    obtain ⟨i,l,hy⟩ := hc y
    refine ⟨p i+l.val,⟨i,l,rfl⟩,?_⟩
    simpa only [sub_add_eq_sub_sub] using hy
  let w : ℝ≥0∞ := ENNReal.ofReal ((2*L)^n)
  have hw0 : w≠0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hwtop : w≠∞ := ENNReal.ofReal_ne_top
  have hpoint (z : Space n) : cubicCenterInfimum K*w≤field Λ p ((cube n (L+r)).indicator (fun _ => 1)) z := by
    have hh := (cubicCenterInfimum_le_window hL hKr (locallyFinite Λ p) hcover z).trans
      (ENNReal.div_le_div_right (count_le_field Λ p z (L+r)) _)
    exact (ENNReal.le_div_iff_mul_le (Or.inl hw0) (Or.inl hwtop)).mp hh
  let := probability_window hF0 hFtop
  have hi := lintegral_mono (μ:=uniformWindow F) hpoint
  rw [lintegral_const,measure_univ,mul_one,normalized_averaging Λ hF p
    (measurable_const.indicator (isCompact_cube n (L+r)).measurableSet),
    lintegral_indicator (isCompact_cube n (L+r)).measurableSet,lintegral_const,
    Measure.restrict_apply_univ,one_mul,volume_cube n hLr] at hi
  have hh := (ENNReal.le_div_iff_mul_le (Or.inl hw0) (Or.inl hwtop)).mpr hi
  have he : ENNReal.ofReal ((2*(L+r))^n)/w = ENNReal.ofReal (((L+r)/L)^n) := by
    dsimp [w]
    rw [← ENNReal.ofReal_div_of_pos (by positivity),← div_pow]
    congr 2
    field_simp
  simpa only [mul_div_assoc,he] using hh

lemma cubic_le_periodic {n : ℕ} {I : Type u_5} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F K : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    (hK : IsCompact K) (hc : ∀ y,∃ (i:I) (l:Λ),y-p i-l.val∈K) :
    cubicCenterInfimum K ≤ (Fintype.card I:ℝ≥0∞)/volume F := by
  obtain ⟨r,hr,hKr⟩ := exists_cube_superset hK
  have heq (L : ℝ) (hL : 0<L) : (L+r)/L=1+r/L := by field_simp
  have ht : Tendsto (fun L : ℝ => ENNReal.ofReal (((L+r)/L)^n)) atTop (𝓝 1) := by
    have hrat := (tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_id.const_div_atTop r)
    have hh := ENNReal.tendsto_ofReal (hrat.pow n)
    simp only [add_zero,one_pow,ENNReal.ofReal_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    simp only [id_eq,heq L hL]
  have ht' : Tendsto (fun L : ℝ => ((Fintype.card I:ℝ≥0∞)/volume F)*ENNReal.ofReal (((L+r)/L)^n)) atTop
      (𝓝 ((Fintype.card I:ℝ≥0∞)/volume F)) := by
    simpa only [mul_one] using (ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.div_ne_top (by finiteness) hF0)))
  apply ge_of_tendsto ht'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact cubic_le_periodic_window Λ p hF hF0 hFtop hL hKr (by linarith only [hL,hr]) hc
end PeriodicEquality

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PeriodicDensity
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory Module
open scoped ENNReal Classical

lemma PeriodicCover.cubic_le {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) (hK : IsCompact K) :
    cubicCenterInfimum K ≤ P.intensity := by
  let := P.discrete
  let := P.fullrank
  let b := Module.Free.chooseBasis ℤ P.lattice
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hF : IsAddFundamentalDomain P.lattice F volume := ZLattice.isAddFundamentalDomain b volume
  have hF0 : volume F≠0 := ZSpan.measure_fundamentalDomain_ne_zero _
  have hFtop : volume F≠∞ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have he : ENNReal.ofReal (ZLattice.covolume P.lattice volume)=volume F := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF,Measure.real,ENNReal.ofReal_toReal hFtop]
  simpa only [PeriodicCover.intensity,he,Fintype.card_fin] using
    PeriodicEquality.cubic_le_periodic P.lattice P.offsets hF hF0 hFtop hK P.covers

lemma CubicCover.toPeriodic_intensity {n : ℕ} {K : Set (Space n)} (P : CubicCover K) :
    P.toPeriodic.intensity = (P.centers.card:ℝ≥0∞)/ENNReal.ofReal ((2*P.L)^n) := by
  dsimp only [PeriodicCover.intensity,CubicCover.toPeriodic]
  congr 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZSpan.isAddFundamentalDomain (CubicLattice.basis n P.L P.positive) volume),
    Measure.real,CubicLattice.volume_domain P.positive,ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]

theorem periodization_all {n : ℕ} {K : Set (Space n)} (hK : ConvexBody K) :
    thetaT K = thetaPerListed K := by
  have hKtop : volume K≠∞ := hK.1.measure_ne_top
  have hK0 : volume K≠0 := ne_of_gt ((isOpen_interior.measure_pos volume hK.2.2).trans_le (measure_mono interior_subset))
  rw [periodization hK]
  apply le_antisymm
  · apply le_iInf
    intro P
    exact mul_le_mul le_rfl (P.cubic_le hK.1) bot_le bot_le
  · rw [cubicCenterInfimum,ENNReal.mul_iInf_of_ne hK0 hKtop]
    apply le_iInf
    intro P
    have hh := iInf_le (fun Q : PeriodicCover K => volume K*Q.intensity) P.toPeriodic
    simpa only [thetaPerListed,CubicCover.toPeriodic_intensity] using hh
end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DistinctCosets
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory
open scoped ENNReal Classical

lemma PeriodicCover.remove_repeats {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) :
    ∃ Q : PeriodicCover K,Q.Distinct ∧ Q.intensity≤P.intensity := by
  let S : Finset (Space n ⧸ P.lattice) := Finset.univ.image P.coset
  have hex (s : S) : ∃ i : Fin P.m,P.coset i=s.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp s.property
    exact ⟨i,hi⟩
  let r : S → Fin P.m := fun s => Classical.choose (hex s)
  have hr (s : S) : P.coset (r s)=s.val := Classical.choose_spec (hex s)
  let e := Finset.equivFin S
  let Q : PeriodicCover K := {
    lattice := P.lattice
    discrete := P.discrete
    fullrank := P.fullrank
    m := S.card
    offsets := fun j => P.offsets (r (e.symm j))
    covers := by
      intro y
      obtain ⟨i,l,hy⟩ := P.covers y
      let s : S := ⟨P.coset i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
      have heq : P.coset i=P.coset (r s) := (hr s).symm
      have hmem : P.offsets i-P.offsets (r s) ∈ P.lattice := (Submodule.Quotient.eq P.lattice).mp heq
      refine ⟨e s,⟨P.offsets i-P.offsets (r s)+l.val,P.lattice.add_mem hmem l.property⟩,?_⟩
      simp only [Equiv.symm_apply_apply]
      have he : y - P.offsets (r s) - (P.offsets i - P.offsets (r s) + l.val) =
          y - P.offsets i - l.val := by abel
      simpa only [he] using hy }
  refine ⟨Q,?_,?_⟩
  · intro j k hjk
    change P.coset (r (e.symm j))=P.coset (r (e.symm k)) at hjk
    rw [hr,hr] at hjk
    exact e.symm.injective (Subtype.ext hjk)
  · change (S.card:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)≤
      (P.m:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)
    apply ENNReal.div_le_div_right
    have hc : S.card≤P.m := by simpa only [S,Finset.card_univ,Fintype.card_fin] using (Finset.card_image_le (s:=Finset.univ) (f:=P.coset))
    exact_mod_cast hc

lemma listed_eq_distinct {n : ℕ} (K : Set (Space n)) : thetaPerListed K=thetaPer K := by
  apply le_antisymm
  · apply le_iInf
    intro P
    exact iInf_le (fun Q : PeriodicCover K => volume K*Q.intensity) P.val
  · apply le_iInf
    intro P
    obtain ⟨Q,hQ,hQP⟩ := P.remove_repeats
    exact (iInf_le (fun Q : {P : PeriodicCover K // P.Distinct} => volume K*Q.val.intensity) ⟨Q,hQ⟩).trans
      (mul_le_mul le_rfl hQP bot_le bot_le)

theorem periodization_exact_oai {n : ℕ} {K : Set (Space n)} (hK : ConvexBody K) :
    thetaT K=thetaPer K := (periodization_all hK).trans (listed_eq_distinct K)
end TranslativeCovering

end OAI
end

theorem solution : type_of% @OAI.TranslativeCovering.periodization_exact_oai := @OAI.TranslativeCovering.periodization_exact_oai
